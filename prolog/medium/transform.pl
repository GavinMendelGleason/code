:- module(transform,[]).

% :- type list(T) --> [] ; [T|list(T)].
isa_list(X,T) :-
    (  X = []
    ;  X = [H|R],
       isa(H,T),
       isa_list(R,T)
    ).

isa(X,T) :-
    var(T),
    !,
    when(T,
         isa(X,T)).
isa(X,T) :-
    T =.. [F|Args],
    atom_concat('isa_',F,G),
    Goal =.. [G,X|Args],
    call(Goal).

/* 
 * negative_metaintepret(Goal, Error) is nondet.
 * 
 * The negative meta-interpreter is intended to resolve the question of a type inclusion 
 * relation |- x : T, for some term x and type T. 
 * 
 * The interpreter takes a *direct* implementation of a predicate which written to determine 
 * inclusion *deterministically* and instead, and is false when |- x : T, and results in a 
 * binding for an error when ¬(|- x : T). 
 * 
 * Because we insist on determinism, all disjunctions *must* be exclusive and are therefore 
 * interpreted as such. We must refrain from utilising negation in the definition of 
 * predicates. 
 * 
 * An example of the direct style of predicates is as follows: 
 * 
 * isa_list(X,T) :-
 *    (  X = []
 *    ;  X = [H|R],
 *       isa_list(R,T)
 *    ).
 * 
 * *OR*
 * 
 * isa_list([],_T).
 * isa_list([H|R],T) :-
 *       isa(H,T),
 *       isa_list(R,T).
 *
 * This is the inclusion predicate which is associated with the following algebraic type:
 *
 * :- type list(T) ---> [] ; [T|list(T)].
 *
 * Types can be defined algebraically as above, and then automatically converted into the direct 
 * style. 
 */
negative_metainterpret(isa_integer(X), Error) :-
    \+ integer(X),
    Error = domain_error(X, M),
    format(atom(M), '~q is not an integer', [X]).
negative_metainterpret(isa(X,T), Error) :-
    % if the type variable is still a variable, we
    % need to suspend the interpretation.
    var(T),
    !,
    when(ground(T),
         negative_metainterpret(isa(X,T),Error)).
negative_metainterpret(isa(X,T), Error) :-
    T =.. [F|Args],
    atom_concat('isa_',F,G),
    Goal =.. [G,X|Args],
    negative_metainterpret(Goal,Error).
negative_metainterpret((TP1,TP2), Error) :-
    (   positive_metainterpret((TP1,TP2))
    ->  fail
    ;   format(atom(M), 'Non viable clauses for conjunction ~q',
               [(TP1,TP2)]),
        Error = domain_error((TP1,TP2),M)
    ).
negative_metainterpret((_TP1,TP2), Error) :-
    negative_metainterpret(TP2, Error).
negative_metainterpret((TP1;TP2), Error) :-
    (   negative_metainterpret(TP1,Error1)
    ->  (   negative_metainterpret(TP2,_)
        ->  Error = domain_error((TP1;TP2), M),
            format(atom(M), 'No viable clauses for disjunction ~q',
                   [(TP1;TP2)])
        ;   Error = Error1)
    ;   (   negative_metainterpret(TP2,Error2)
        ->  Error = Error2
        ;   Error = domain_error((TP1;TP2),M),
            format(atom(M),'Too many available clause for disjunction ~q', [(TP1;TP2)])
        )
    ).
negative_metainterpret((TP1=TP2), domain_error((TP1=TP2),Msg)) :-
    \+ TP1=TP2,
    format(atom(Msg), 'Non unifiable term elements ~q and ~q', [TP1,TP2]).
negative_metainterpret(P, Error) :-
    functor(P,F,_),
    \+ member(F,[isa,isa_integer,',',';', '=']),
    !,
    bagof(E,(clause(P, Body),
             (   negative_metainterpret(Body,E)
             ->  true
             ;   E = none)),
          Errors),
    include([none]>>(true), Errors, Results),
    (   Results = []
    ->  Error = domain_error(P, M),
        format(atom(M), 'No available clause for predicate ~q', [P])
    ;   Results = [_,_|_]
    ->  Error = domain_error(P, M),
        format(atom(M), 'Too many viable clauses for predicate ~q',
               [P])
    ;   fail).

positive_metainterpret(T1=T2) :-
    T1 = T2.
positive_metainterpret((T1,T2)) :-
    positive_metainterpret(T1),
    positive_metainterpret(T2).
positive_metainterpret(C) :-
    functor(C,F,_),
    \+ member(F,[',','=']),
    \+ negative_metainterpret(C,_).

