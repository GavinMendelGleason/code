:- module(guard, [
              '|'/2,
              '*'/1,
              op(920,fy, *)
              % op(1005,xfy,'|').
          ]).

:- use_module(library(clpr)).
:- use_module(types, []).
:- use_module(boundness, []).
:- use_module(clpad, [domain/2]).
:- use_module(library(plunit)).

:- op(601, xfx, @).
%:- op(1005,xfy,'|').

/*
 * A guard is just a conjunction really.
 *
 */
'|'(A,B) :-
    call(A),
    call(B).

/*
 * Forget the next phrase.
 *
 * Useful for declarative debugging.
 */
*_.

% We don't want to apply recursively to ourselves!
module_wants_guard(Module) :-
    Module \= guard,
    predicate_property(Module:'|'(_,_), imported_from(guard)).

bodyless_predicate(Term) :-
    \+ Term = (:-_),
    \+ Term = (_:-_),
    \+ Term = (_-->_),
    \+ Term = end_of_file.

safe_guard_predicate(number(_)).
safe_guard_predicate(integer(_)).
safe_guard_predicate(string(_)).
safe_guard_predicate(atom(_)).
safe_guard_predicate(list(_)).
safe_guard_predicate(var(_)).
safe_guard_predicate(nonvar(_)).
safe_guard_predicate(ground(_)).
safe_guard_predicate(_<_).
safe_guard_predicate(_>_).
safe_guard_predicate(_>=_).
safe_guard_predicate(_=<_).

safe_guard(A) :-
    safe_guard_predicate(A),
    !.
safe_guard((A,B)) :-
    safe_guard(A),
    safe_guard(B).
safe_guard((A;B)) :-
    safe_guard(A),
    safe_guard(B).

has_guard(A | B, A, B) :-
    safe_guard(A).

:- begin_tests(safe_guard).

test(conjunction,[]) :-
    safe_guard(
        (   list(X),
            ground(X))).

test(disjunction,[]) :-
    safe_guard(
        (   var(X)
        ;   atom(X))).

test(mixed,[]) :-
    safe_guard(
        (   var(X)
        ;   integer(X),
            X > 1)).

:- end_tests(safe_guard).


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

guard_constraint(X=Y,X=Y).
guard_constraint(ground(X),domain(X,ground@boundness)).
guard_constraint(nonvar(X),domain(X,nonvar@boundness)).
guard_constraint(var(X),domain(X,var@boundness)).
guard_constraint(list(X),(domain(X,list@types),
                          domain(X,nonvar@boundness))).
guard_constraint(number(X),(domain(X,number@types),
                            domain(X,ground@boundness))).
guard_constraint(string(X),(domain(X,string@types),
                            domain(X,ground@boundness))).
guard_constraint(integer(X),(domain(X,intger@types),
                             domain(X,ground@boundness))).
guard_constraint(atom(X),(domain(X,atom@types),
                          domain(X,ground@boundness))).
guard_constraint((A<B),{A<B}).
guard_constraint((A>B),{A>B}).
guard_constraint((A>=B),{A>=B}).
guard_constraint((A=<B),{A=<B}).
guard_constraint((A,B),(AC,BC)) :-
    guard_constraint(A,AC),
    guard_constraint(B,BC).
guard_constraint((A;B),(AC;BC)) :-
    guard_constraint(A,AC),
    guard_constraint(B,BC).

constraint_goal(Arg_Template,Args,Guard,Goal) :-
    maplist([X,Y,X=Y]>>true,Arg_Template,Args,Equality_List),
    xfy_list(',',Equations,Equality_List),
    guard_constraint(Guard,Constraint),
    Goal = (Equations,Constraint).

:- begin_tests(guard_constraints).

test(exclusive_numbers,[]) :-
    Arg_Template = [_A,_B,_C],

    Args_1 = [a,X,_Y],
    Guard_1 = (integer(X),X > 0),

    Args_2 = [a,Z,_W],
    Guard_2 = (integer(Z), Z < 0),

    constraint_goal(Arg_Template,Args_1,Guard_1,Goal_1),
    constraint_goal(Arg_Template,Args_2,Guard_2,Goal_2),
    \+ call((Goal_1,Goal_2)).


test(exclusive_binding,[]) :-
    Arg_Template = [_A,_B],

    Args_1 = [X,_Y],
    Guard_1 = var(X),

    Args_2 = [Z,_W],
    Guard_2 = (integer(Z), Z < 0),

    constraint_goal(Arg_Template,Args_1,Guard_1,Goal_1),
    constraint_goal(Arg_Template,Args_2,Guard_2,Goal_2),
    \+ call((Goal_1,Goal_2)).

test(overlapping_binding,[]) :-
    Arg_Template = [_A,_B],

    Args_1 = [X,_Y],
    Guard_1 = ground(X),

    Args_2 = [Z,_W],
    Guard_2 = nonvar(Z),

    constraint_goal(Arg_Template,Args_1,Guard_1,Goal_1),
    constraint_goal(Arg_Template,Args_2,Guard_2,Goal_2),
    call((Goal_1,Goal_2)).

test(equality_exclusion,[]) :-
    Arg_Template = [_A,_B],

    Args_1 = [a,Y],
    Guard_1 = ground(Y),

    Args_2 = [b,W],
    Guard_2 = nonvar(W),

    constraint_goal(Arg_Template,Args_1,Guard_1,Goal_1),
    constraint_goal(Arg_Template,Args_2,Guard_2,Goal_2),
    \+ call((Goal_1,Goal_2)).

:- end_tests(guard_constraints).

% Note: Obviously this should be smarter.
trim_negatives(Guard,_Negatives,Guard).

transform_clauses_([],_PN,_Negatives,[]).
transform_clauses_([Args-Guard-Remainder|After],P/N,Negatives,[New_Clause|New_Clauses]) :-
    length(Arg_Template,N),
    constraint_goal(Arg_Template,Args,Guard,Goal),
    forall(
        (   member(Alt_Args-Alt_Guard-_,After),
            constraint_goal(Arg_Template,Alt_Args,Alt_Guard,Alt_Goal)
        ),
        % there are no overlapping guards
        (   call((Goal,Alt_Goal))
        ->  Head_A =.. [P,Args],
            Head_B =.. [P,Alt_Args],
            % Throw? Or warn?  Settable is best.
            format('~NWarning! Overlapping clauses: ~n~q~n~n~q~n~n', [
                       (Head_A :- Guard| ...),
                       (Head_B :- Alt_Guard| ...)
                       ])
        ;   true)
    ),
    % Save to guard
    !,
    % Cut is safe - so is removal of negatives...
    trim_negatives(Guard,Negatives,Trimmed_Guard),
    Head =.. [P|Args],
    New_Clause=(
        Head :- Trimmed_Guard, !, Remainder
    ),
    % Currently doing
    transform_clauses_(After,P/N,[Guard|Negatives],New_Clauses).
transform_clauses_([Args-Guard-Remainder|After],P/N,Negatives,[New_Clause|New_Clauses]) :-
    Head =.. [P|Args],
    New_Clause=(
        Head :- Guard, Remainder
    ),
    transform_clauses_(After,P/N,[Guard|Negatives],New_Clauses).

transform_clauses(P/N, Clauses, New_Clauses) :-
    transform_clauses_(Clauses,P/N,[],New_Clauses).

transformed_clauses(Transformed) :-
    setof(Args-Guard-Remainder,
          clause_to_transform(P/N,Args,Guard,Remainder),
          Clauses),
    transform_clauses(P/N, Clauses, Transformed_Stack),
    reverse(Transformed_Stack,Transformed).

split_guarded_clause((Head :- Body), Head, Guard, Remainder) :-
    has_guard(Body,Guard,Remainder).

/*
 * We store clauses for module wide analysis in clause_to_transform/4
 */
:- dynamic clause_to_transform/4.

:- begin_tests(transform_clauses).

test(split_headless,[]) :-
    \+ split_guarded_clause(p(_X), _Head, _Guard, _Remainder).

test(split_no_guard,[]) :-
    \+ split_guarded_clause(
           (   p(X) :-
                   X = 1
           ),
           _Head, _Guard, _Remainder).

test(split_head,[]) :-
    split_guarded_clause(
        (
            p(X) :-
                X > 1
                | X = 30
        ),
        Head, Guard, Body),
    Head = p(A),
    Guard = (A > 1),
    Body = (A = 30).

test(split_complex_guard,[]) :-
    split_guarded_clause(
        (
            p(X) :-
                X > 1,
                (   integer(X)
                ;   number(X))
                | X = 30
        ),
        Head, Guard, Body),
    Head = p(A),
    Guard = ( A > 1, (integer(A);number(A))),
    Body = (A = 30).

test(transform_clause, []) :-

    retractall(clause_to_transform(_,_,_,_)),

    Clause_1 = (
        abs(X,Y) :-
            X >= 0
            | X = Y
    ),

    split_guarded_clause(Clause_1,Head_1,Guard_1,Remainder_1),
    Head_1 =.. [P_1|Args_1],
    length(Args_1,N_1),
    assertz(guard:clause_to_transform(P_1/N_1,Args_1,Guard_1,Remainder_1)),

    Clause_2 = (
        abs(A,B) :-
            A < 0
            | B is -A
    ),

    split_guarded_clause(Clause_2,Head_2,Guard_2,Remainder_2),
    Head_2 =.. [P_2|Args_2],
    length(Args_2,N_2),
    assertz(guard:clause_to_transform(P_2/N_2,Args_2,Guard_2,Remainder_2)),

    transformed_clauses(Clauses),
    Clauses = [(abs(Arg1_1, Arg1_2):- Arg1_1 >=0, !, Arg1_1 = Arg1_2),
               (abs(Arg2_1, Arg2_2):- Arg2_1 <0, !, Arg2_2 is -Arg2_1)],

    retractall(guard:clause_to_transform(_,_,_,_)).


:- end_tests(transform_clauses).

user:term_expansion(begin_of_file, []) :-
    % We don't want to process ourselves, so fail...
    prolog_load_context(module, Module),
    guard:module_wants_guard(Module),
    retractall(clause_to_transform(_,_,_,_)).
user:term_expansion(end_of_file,Clauses) :-
    prolog_load_context(module, Module),
    guard:module_wants_guard(Module),
    guard:transformed_clauses(Clauses),
    writeq(Clauses),
    nl.
user:term_expansion(Clause, No_Clause) :-
    prolog_load_context(module, Module),
    guard:module_wants_guard(Module),
    guard:split_guarded_clause(Clause,Head,Guard,Remainder),
    !,
    Head =.. [P|Args],
    length(Args,N),
    assertz(guard:clause_to_transform(P/N,Args,Guard,Remainder)),
    No_Clause = [].
