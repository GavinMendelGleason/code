%:- module(first_blog,[]).

:- use_module(library(type_check)).

:- type term ---> term_a ; term_b.

:- pred p(term).
p(term_a) :- write(term_a) :: write(any).
p(term_b) :- write(term_b) :: write(any).

:- pred q.
q :- p(term_c).
