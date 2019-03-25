:- module(balanced_ternary, [
              dtw/3,
              add/3,
              subtract/3
          ]).

:- use_module(library(clpfd)).

/* How does this not exist? in ISO? */
log(N,B,0) :-
    B #> N.
log(N,B,Ans) :-
    N1 #= N // B,
    N1 #> 0,
    log(N1, B, A),
    Ans #= A + 1.

decimal_ternary_word(Int,Word,WS) :-
    decimal_ternary(Int,Rep),
    zero_pad(Rep,WS,Word).

% just short-hand
dtw(Int,Rep,WS) :-
    decimal_ternary_word(Int,Rep,WS).

decimal_ternary(Int,Rep) :-
    log(Int,2,R),
    decimal_ternary_aux(Int,R,Rep).

decimal_ternary_aux(0, 0, [0]).
decimal_ternary_aux(1, 0, [1]).
decimal_ternary_aux(Int,R,[D|Rep]) :-
    Int #>= 0, R #>= 0,
    P is 2 ** R,
    D #= Int // P,
    Rem #= Int - D * P,
    R1 #= R - 1,
    decimal_ternary_aux(Rem,R1,Rep).

ternary_decimal(W,N) :-
    length(W,WS),
    Exp #= WS - 1,
    ternary_decimal_aux(W,N,Exp).

% just shorthand
td(W,N) :-
    ternary_decimal(W,N).

ternary_decimal_aux([],0,-1).
ternary_decimal_aux([A|R],M,Exp) :-
    New_Exp #= Exp - 1,
    ternary_decimal_aux(R,N,New_Exp),
    Order is (2 ** Exp),
    M #= N + A * Order.

zeros(0,[]).
zeros(N, [0|R]) :-
    N #> 0,
    M #= N - 1,
    zeros(M,R).

zero_pad(L,WS,Word) :-
    length(L,R),
    R #=< WS,
    P #= WS - R,
    zeros(P, Top),
    append(Top,L,Word).

overflow([B0,B1|_]) :-
    (   B0 in -1 \/ 1 
    ;   B1 in -1 \/ 1).

no_overflow([0,0|_]).

neg_bit( 1,-1).
neg_bit(-1, 1).
neg_bit( 0, 0).

neg([],[]).
neg([B|Rest],[BN|NRest]) :-
    neg(Rest,NRest),
    neg_bit(B,BN).

% a normal trit
trit( 1).
trit( 0).
trit(-1).

% The other types are just documentation...

% unbalanced negative trit
ubn_trit(  0).
ubn_trit( -1).
ubn_trit( -2).

% bit
bit(0).
bit(1).

% negative bit
n_bit( 0).
n_bit(-1).

/* shift the top off */
shift([B|A],R) :-
    % generator / test
    trit(B),
    shift_aux(A,R).

shift_aux([], [0]).
shift_aux([A|R], [A|RS]) :-
    shift_aux(R,RS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Some very mysterious operations!

%%%%%%%%%%%%%%%%%
% op0(X,Y, (T : Z))
%
% X a trit
% Y a trit
% T a bit
% Z an unbalanced negative trit {0,-1,-2}
%
% T is a kind of "overflow" which we will shift, Z a leftover.
%
% We will sometimes shift an overflow balanced by subtraction in Z.
%
% Doing someting similar in op1/3 will give keep us from having to cascade.
%
% The proof of this would be cool!
op0( 1, 1,(1 :  0)).
op0( 0, 1,(1 : -1)).
op0(-1, 1,(0 :  0)).
op0( 1, 0,(1 : -1)).
op0( 0, 0,(0 :  0)).
op0(-1, 0,(0 : -1)).
op0( 1,-1,(0 :  0)).
op0( 0,-1,(0 : -1)).
op0(-1,-1,(0 : -2)).

%%%%%%%%%%%%%%%%%
% op1(X,Y,(T : Z))
%
% X a bit
% Y an unbalnced negative trit {0,-1,-2}
% T a negative bit {-1,0}
% Z a bit
%
% We can now move some of the excessive negativity over to the left
% (remember, T will be shifted) where it can act as a normal trit again
op1(1,-2,(-1 : 1)).
op1(0,-2,(-1 : 0)).
op1(1,-1,( 0 : 0)).
op1(0,-1,(-1 : 1)).
op1(1, 0,( 0 : 1)).
op1(0, 0,( 0 : 0)).

%%%%%%%%%%%%%%%%%
% op2(X,Y,W)
%
% X a negative bit {-1,0}
% Y a bit
% W a trit
op2(-1,0,-1).
op2( 0,0, 0).
op2(-1,1, 0).
op2( 0,1, 1).

/* 
 * The punchline! Addition in only 3 operations. 
 */
add(X,Y,W) :-
    maplist([BX,BY,BT,BZ]>>( op0(BX,BY,(BT:BZ)) ), X, Y, T, Z),
    shift(T,TS),
    maplist([BT,BZ,BT1,BZ1]>>( op1(BT,BZ,(BT1:BZ1)) ), TS, Z, T1, Z1),
    shift(T1,T1S), 
    maplist([BT1,BZ1,BW]>>( op2(BT1,BZ1,BW) ), T1S, Z1, W).

/* 
 * Subtraction in only 4
 */
subtract(X,Y,W) :-
    neg(Y,YN),
    add(X,YN,W).

is_zero(L) :-
    maplist([B]>>(B=0),L).

equal(X,Y) :-
    subtract(X,Y,W),
    is_zero(W).

/************************
 *  Examples 

***************
** Add 13 and 6 

% word size of 8, 
WS = 8, 
% translate 13 and 6 into balanced ternary
dtw(13,X,WS), dtw(6,Y,WS), 
add(X,Y,Z), 
% Hopefully we got 19, let's check. 
dtw(19,K,WS),
% we can eyeball Zero easily enough
subtract(Z,K,Zero).
%, but look at Z..., different from K

*********************************
** Generate other representations

% We can find alternative representations of a number by running the addition search backwards, 
% and finding everything which would bring us to zero. We can then negate this value
% to get a number equal to the original. 

% word size
WS = 8, 
% choose a number
N = 6, 
dtw(3,X,6), 
% Get the unique representation of zero
dtw(0,Zero,6), 
% Add something unspecified to X to get zero
add(X, XN, Zero), 
% invert this
neg(XN,Other_X).

% Unfortunately this answer gives us a lot of nonsense with large negative numbers.
% The reason is that our operations are really only safe if we leave a couple of "guard bits" 
% at the top of our word to make sure we don't overflow.

% ... take the lines above
% ... and add this to the end
no_overflow(Other_X). 

% Now we get some nice representations! Check to see if equal(X,Other_X)!
% 
% Are these all of the representations? I think so!
 

 */
