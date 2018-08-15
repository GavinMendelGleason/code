module(test,[]).

/* 



*/

user:goal_expansion(T :- P,test,T :- P) :- writeq(T :- P).


     
term_expansion(X, X) :-
	debug(expand, '~q', [X]).

a(a).
a(b).
a(c).


b(X) :- c(X).
b(3).

c(4).
c(5).


:- meta_predicate  d(0).

d(X) :-  call(X).

e(X) :- d(c(X)).
