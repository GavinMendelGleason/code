:- module(pred,[]).



pred(X) :-
    writeq(X).
   
:- pred length.
% "Computes the length of L.".
%:- pred length(L,N) : var * integer => list * integer .
% "Outputs L of length N.".
%:- pred length(L,N) : list * integer => list * integer .

% "Checks that L is of length N.".

length([],0).
length([H|T],N) :-
    length(T,M),
    add(M, 1, N).


    
