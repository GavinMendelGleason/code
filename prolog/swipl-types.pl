:- module(swipl_types,[],[]).

:- use_module(library(mavis)).

%% even(+X:integer) is semidet.
even(X) :-
    0 is X mod 2.
