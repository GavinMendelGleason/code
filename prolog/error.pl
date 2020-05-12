:- module(error, []).

binding_set(A) :-
    is_list(A).
 
true(A) :-
    binding_set(A).

mgu(A,B,C) :- 
    forall(member(X,A),
           member(X,B)),
    forall(member(X,B),
           member(X,A)),
    union(A,B,C).

%'<<'(A,B) :- 

and(true(A), true(B), true(C)) :-
    mgu(A,B,C).
and(true(A), false, false).
and(false, true(B), false).
and(false, false, false).
and(error(A), true(_), error(A)).
and(true(_), error(B), error(B)).
and(error(A), false, error(A)).
and(false, error(B), error(B)).
and(error(A), error(B), error(A)).
and(error(A), error(B), error(B)).

or(false, true(B), true(B)).
or(true(A), false, true(A)).
or(true(A), true(B), true(A)).
or(true(A), true(B), true(B)).
or(error(A), true(_), error(A)).
or(true(_), error(B), error(B)).
or(error(A), false, error(A)).
or(false, error(B), error(B)).
or(error(A), error(B), error(A)).
or(error(A), error(B), error(B)).

mint(A=B,R) :-
    (   A=B
    *-> R=true([A=B])
    ;   R=false).
mint(error(A), error(A)).
mint((A,B), C) :-
    and(A,B,C).
mint((A;B), C) :-
    or(A,B,C).

