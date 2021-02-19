:- module(ik2tree, [
              dkw/3,
              decimal_kary/3,
              kd/3,
              kary_decimal/3,
              triples_to_k_vectors/4
          ]).

/*
 * Interleaved K^2 tree
 *
 * Interleaved K^2 trees are efficient methods of storing
 * ternary relationships
 *
 *
 */

:- use_module(library(clpfd)).

/*
 * k2 tree and persistent k2 tree prototypes
 */
/* How does this not exist? in ISO? */
log(N,B,0) :-
    B #> N.
log(N,B,Ans) :-
    N1 #= N // B,
    N1 #> 0,
    log(N1, B, A),
    Ans #= A + 1.

decimal_kary_word(Int,K,Word,WS) :-
    decimal_kary(Int,K,Rep),
    zero_pad(Rep,WS,Word).

% just short-hand
dkw(Int,K,WS) :-
    decimal_kary(Int,K,WS).

decimal_kary(Int,K,Rep) :-
    once(log(Int,K,R)),
    once(decimal_kary_aux(Int,K,R,Rep)).

decimal_kary(Int,K,N,Word) :-
    once(log(N,K,R)),
    once(decimal_kary_aux(Int,K,R,Word)).

decimal_kary_aux(Int, _, 0, [Int]).
decimal_kary_aux(Int, K, R,[D|Rep]) :-
    Int #>= 0, R #>= 0,
    P is K ** R,
    D #= Int // P,
    Rem #= Int - D * P,
    R1 #= R - 1,
    decimal_kary_aux(Rem,K,R1,Rep).

kary_decimal(W,K,N) :-
    length(W,WS),
    Exp #= WS - 1,
    kary_decimal_aux(W,K,N,Exp).

% just shorthand
kd(W,K,N) :-
    kary_decimal(W,K,N).

kary_decimal_aux([],_,0,-1).
kary_decimal_aux([A|R],K,M,Exp) :-
    New_Exp #= Exp - 1,
    kary_decimal_aux(R,K,N,New_Exp),
    Order is (K ** Exp),
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

empty_ik2_tree(I,K,N,Tree) :-
    Tree =
    ik2_tree{
        n : N,
        k : K,
        i : I,
        l : [],
        t : []
    }.

prefix(_, 0, []).
prefix([X|T], N, [X|L]) :-
    N #> 0,
    M #= N - 1,
    prefix(T, M, L).

prefix_or_zeros(T,Size,Level) :-
    length(T,Length),
    (   Length =< Size
    ->  zero_pad(T,Size,Level)
    ;   prefix(T,Size,Level)
    ).

:- meta_predicate assuming(0).
assuming(G) :-
    (   G
    ->  true
    ;   throw(error(assertion_failed(G)))).

create_dictionaries(Triples,Dictionaries) :-
    maplist([t(X,Y,Z),X,Y,Z]>>true,Triples, Subjects, Predicates, Objects),
    convlist([value(V),V]>>true, Objects, Values),
    convlist([node(N),N]>>true, Objects, Nodes),
    append(Subjects, Nodes, All_Nodes),
    sort(All_Nodes,Sorted_Nodes),
    sort(Predicates,Sorted_Predicates),
    sort(Values,Sorted_Values),
    length(Sorted_Nodes, Value_Offset),
    append([Subjects, Nodes], Total),
    length(Total, N),
    length(Sorted_Predicates, I),
    Dictionaries = dictionaries{
                       i: I,
                       n: N,
                       nodes: Sorted_Nodes,
                       predicates: Sorted_Predicates,
                       value_offset: Value_Offset,
                       values: Sorted_Values
                   }.

predicate_id(Predicate, Dictionaries, ID) :-
    Predicates = (Dictionaries.predicates),
    once(nth0(ID,Predicates,Predicate)).

node_id(Node, Dictionaries, ID) :-
    Nodes = (Dictionaries.nodes),
    once(nth0(ID,Nodes,Node)).

subject_id(Node, Dictionaries, ID) :-
    node_id(Node, Dictionaries, ID).

value_id(Value, Dictionaries, ID) :-
    Values = (Dictionaries.values),
    once(nth0(Pre_ID,Values,Value)),
    ID #= Pre_ID + (Dictionaries.value_offset).

object_id(value(Value), Dictionaries, ID) :-
    value_id(Value, Dictionaries, ID).
object_id(node(Node), Dictionaries, ID) :-
    node_id(Node, Dictionaries, ID).

triples_to_k_vectors(Triples, Dictionaries, K, [Ss,Ps,Os]) :-
    create_dictionaries(Triples,Dictionaries),

    Values = (Dictionaries.values),
    N = (Dictionaries.n),

    maplist({K,N,Dictionaries}/[t(S,P,O),SL,PID,OL]>>(
                subject_id(S,Dictionaries, SID),
                decimal_kary(SID,K,N,SL),
                object_id(O,Dictionaries, OID),
                decimal_kary(OID,K,N,OL),
                predicate_id(P,Dictionaries, PID)
            ),
            Triples,Ss,Ps,Os).

triples_ik2_tree(Triples, K, Ik2tree) :-
    triples_to_k_vectors(Triples, Dictionaries, K, [Ss,Ps,Os]),
    EmptyTree =
    ik2tree{
        k: K,
        dictionaries: Dictionaries, % I in dictionaries
        l: L
        t: T
    },
    %  transpose S and O
    transpose(Ss,ST),
    transpose(Os,OT),
    build_ik2_tree(ST,OT,Ps, Dictionaries, K, EmptyTree, Ik2Tree).

build_ik2_tree([], [], Ps, _, _, Tree, Tree).
build_ik2_tree([SL|SN], [OL|ON], Ps, Dictionaries, K, Tree, Final_Tree) :-
    % 1. find |Y| at previous level (or size of all |Y| for first) - this is I
    % 2. Use K to form I * K cells with ones based on each Y and S/P
    Level = K * T,
    maplist([MSB
    true.

build_ik2_tree(Ss,Os,Ps, Dictionaries, K, Tree) :-
    build_ik2_tree(Ss,Os,Ps, Dictionaries, K, Empty_Tree, Final_Tree).

:- begin_tests(insert_triples).

test(triples_to_k_vectors, []) :-

    triples_to_k_vectors([t(a,b,node(c)), t(c,e,node(f))], D, 2, R),

    D = dictionaries{n:4, nodes:[a, c, f], predicates:[b, e], value_offset:3, values:[]},
    R = [[[0, 0, 0], [0, 0, 1]], [0, 1], [[0, 0, 1], [0, 1, 0]]].

test(build_ik2_tree, []) :-
    true.

:- end_tests(insert_triples).


/*

[[[0,0],[0,0],[0,1]], [0,1], [[0,0],[0,1],[1,0]]]


*   *
|\ /\
. . .
|\|\|\
......


[1,1,2]
 |
 1

 1
 |
[0,1,2]



% (a,b)  (c,d)      [a,b,c,d]

  0,1     2,3

   0 1 | 2 3     K = 2
   ---------
0 | 0 0 | 0 0
1 | 1 0 | 0 0        1001
  |----------    0010   0010
2 | 0 0 | 0 0
3 | 0 0 | 1 0


N = 4

   0 1 | 2 3     K = 2
   ----------
0 | 0 0 | 0 0 |
1 | 1 0 | 0 0 |        1001
  |---------- |    0010   0010
2 | 0 0 | 0 0 |
3 | 0 0 | 1 0 |
  ------------

% (a,p,b)  (c,q,d)      [a,b,c,d]  [p,q]   |[p,q]| = 2

   0 1 | 2 3         K = 2,  I=|predicates|    Previous, Deleted
   -----------
0 | 0 0 | 0 0 |
1 | 1 0 | 0 0 |      (p) 1000  (q) 0001
  |---------- |       0010            0010
2 | 0 0 | 0 0 |
3 | 0 0 | 1 0 |
  ------------

% .->.->.->   X,Y,Z


But how do we deal with deletions? We can expand I to include
+p, or -p, op






*/
