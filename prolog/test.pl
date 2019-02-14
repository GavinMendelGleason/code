module(test,[]).

set(X1,X2,graph,Z1,Z2) :-
    X1=semantics_graph(Z1,O,I,D,B), 
    X2=semantics_graph(Z2,O,I,D,B).
