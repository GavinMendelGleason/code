:- module(guard_testing, [
              abs/2
          ]).

:- use_module(guard).

abs(X,Y) :-
    X >= 0
    | X = Y,
      format('~NGreater: ~n', [X]).
abs(X,Y) :-
    X < 0
    | Y is -X,
      format('~NLess: ~n', [X]).

my_pred(a,X,Y) :-
    X > 0
    | Y is 13 / X.
my_pred(b,X,Y) :-
    true
    | Y is 13 / X.
