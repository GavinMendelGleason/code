:- module(retry,[]).


retry(N,P) :-
    between(0,3,N),
    
