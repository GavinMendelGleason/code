:- module(types,[],[]).

:- use_module(library(assertions)).
       
/*

nrev([]) := [].
nrev([H|L]) := ~conc(nrev(L),[H]).

:- pred conc(A,B,C) : list(A) => size_ub(C,length(A)+length(B)) + steps_o(length(A)).

conc([],   L) := L.
conc([H|L],K) := [ H | conc(L,K) ].
*/ 
