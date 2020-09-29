:- module(regular, [mi/3]).

/*
 * TODO: Check to make sure clauses starting at predicate P are regular
 *
 * regular(P) :- ...
 */
:- meta_predicate try_or_die(:,?).
try_or_die(Goal, Error) :-
    (   call(Goal)
    *->  true
    ;   throw(Error)).

/* Check well formedness of unambiguous grammars */
:- meta_predicate mi(:,?,?).
mi(true, _,_).
mi(X=Y, _,_) :- X = Y.
mi((A,B), Stack, Term) :-
    !,
    try_or_die(mi(A, [(',',0),Stack], Term),
               error(not_well_formed_ast(Predicate,[(',',0)|Stack],Term))),
    try_or_die(mi(B, [(',',0),Stack], Term),
               error(not_well_formed_ast(Predicate,[(',',1)|Stack],Term))).
mi((A;B), Stack, Term) :-
    !,
    try_or_die((   mi(A, [(';',0),Stack], Term)
               ;   mi(B, [(';',0),Stack], Term)),
               error(not_well_formed_ast((A;B),Stack,Term))).
mi(P, Stack, Term) :-
    strip_module(P, Module, Pred),
    functor(Pred,F,N),
    \+ member(F/N,[','/2,';'/2, '='/2, true/0, is/2]),
    !,
    length(Vars,N),
    Pred =.. [F|Args],
    Q =.. [F|Vars],
    try_or_die(
        (clause(Module:Q, Body),
         Vars = Args,
         mi(Body,[Pred|Stack],Term)),
        error(not_well_formed_ast(Q,[Pred|Stack],Term))).

:- multifile prolog:message//1.
prolog:message(error(not_well_formed_ast(Q, Stack, Term))) -->
        [ 'Not a well formed term: ~q, focusing on: ~q at ~q'-[Q,Term,Stack] ].

