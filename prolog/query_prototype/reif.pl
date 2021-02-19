:- module(reify, [
              reify_reflect/2,
              program_predicate_clauses/3,
              declarations/2
          ]).

/*
 * xfy_list(Op, Term, List) is det.
 *
 * Folds a functor over a list.
 */
xfy_list(Op, Term, [Left|List]) :-
    Term =.. [Op, Left, Right],
    xfy_list(Op, Right, List),
    !.
xfy_list(_, Term, [Term]).

/*
 * reify_reflect(+,-) is det.
 * reify_reflect(-,+) is det.
 */
reify_reflect((:- Body),declaration(Clauses)) :-
    !,
    xfy_list(',', Body, Clauses).
reify_reflect((Head --> Body),clause(P//N,Args,Clauses)) :-
    Head =.. [P|Args],
    length(Args,N),
    xfy_list(',', Body, Clauses),
    !.
reify_reflect((Head :- Body),clause(P/N,Args,[Clause|Clauses])) :-
    Head =.. [P|Args],
    length(Args,N),
    xfy_list(',', Body, [Clause|Clauses]),
    !.
reify_reflect(Head,clause(P/N,Args,[])) :-
    Head =.. [P|Args],
    length(Args,N).

/* Pred is P/N or P//N
 */
program_predicate_clauses(Program,Pred,Clauses) :-
    bagof(
        Clause,
        Args^Body^(   member(Clause,Program),
                      Clause = clause(Pred,Args,Body)),
        Clauses).

declarations(Program,Declarations) :-
    bagof(
        Declaration,
        (   member(Declaration,Program),
            Declaration = declaration(_)),
        Declarations).

:- use_module(library(plunit)).

:- begin_tests(reify).

test(reify_predicate_clause, []) :-

    Term = (p(X) :- X = 1),

    reify_reflect(Term,Reflected),
    Reflected = clause(p/1,[Y],[Y=1]).

test(reify_headless_clause, []) :-

    Term = (p(_)),

    reify_reflect(Term,Reflected),
    Reflected = clause(p/1,[_],[]).

test(reflect_headless_clause, []) :-

    Clause = clause(p/1,[_],[]),

    reify_reflect(Term,Clause),
    Term = p(_).

test(reflect_predicate_clause, []) :-

    Clause = clause(p/1,[_],[q]),

    reify_reflect(Term,Clause),
    Term = (p(_):-q).

test(reflect_declaration, []) :-

    Clause = declaration([q]),

    reify_reflect(Term,Clause),
    Term = (:- q).

test(program_predicate_clauses, []) :-

    Program = [clause(p/1,[x],[q]),
               clause(p/1,[y],[r]),
               clause(q/0,[],[]),
               clause(r/0,[],[])],

    program_predicate_clauses(Program, p/1, P_Clauses),
    P_Clauses  = [clause(p/1,[x],[q]),clause(p/1,[y],[r])],
    program_predicate_clauses(Program, q/0, Q_Clauses),
    Q_Clauses  = [clause(q/0,[],[])],
    program_predicate_clauses(Program, r/0, R_Clauses),
    R_Clauses  = [clause(r/0,[],[])].


test(declaration_clauses, []) :-

    Program = [declaration([module(q,[])]),
               clause(p/1,[y],[r]),
               clause(p/0,[],[]),
               clause(p/1,[z],[s])],

    declarations(Program, Decl),
    Decl = [declaration([module(q,[])])].


:- end_tests(reify).
