:- module(yaag, [sol_set/2,sol_bag/2]).

/*
 * Yet another aggregation library
 */
:- meta_predicate sol_set(1,?).
sol_set(Predicate,Result) :-
    findall(Template,
            call(Predicate, Template),
            Templates),
    sort(Templates, Result).

:- meta_predicate sol_bag(1,?).
sol_bag(Predicate,Result) :-
    findall(Template,
            call(Predicate, Template),
            Result).
