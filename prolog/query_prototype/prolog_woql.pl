:- module(prolog_woql, [
              prolog_ast/2
          ]).

prolog_woql(Term,Woql) :-
    % pre term and term bindings here..
    prolog_woql_goal(Term,Woql).

prolog_woql_goal((A,B),(A,B)) :-
    !.
prolog_woql_goal((A;B),(A;B)) :-
    !.
prolog_woql_goal(Predicate,p(Woql)) :-
    prolog_predicate_woql(Predicate, Woql),
    !.

prolog_predicate_woql(Predicate, Result) :-
    Predicate =.. [F|Args],
    prolog_term_woql_term(Args,WOQL_Args).

prolog_term_woql_term(Var, Term) :-
    var(Var),
    !,
    true.
prolog_term_woql_term(Dict, Dict) :-
    is_dict(Dict),
    !.
prolog_term_woql_term(Dict, Dict) :-
    is_dict(Dict),
    !.
prolog_term_woql_term(Atom, n(Atom)) :-
    atom(Atom),
    !.
prolog_term_woql_term(Atom, n(Atom)) :-
    atom(Atom),
    !.
prolog_term_woql_term(X^^Ty, l(X^^Ty)) :-
    !.
prolog_term_woql_term(X@Lang, l(X@Lang)).
