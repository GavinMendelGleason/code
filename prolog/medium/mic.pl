:- module(mic,[metainterpret/2]).

/* <module> Metainterpertation critic 
 * 
 * mic gives us some information as to causes of failure for a restricted subset of 
 * prolog in which ';' is interpreted as exclusive disjunction.
 * 
 * From the error tree, which is a kind of recording of the failed SLD tree, we can 
 * then determine a likely target for "most interesting failure", for instance 
 * by looking for those resolution paths of greatest depth.
 * 
 * This library is useful for creating either an ad-hoc type-checker which 
 * verifies syntax of a term (well-formedness conditions etc.) or for creating 
 * a full fledged type checker. 
 *
 * Author: Gavin Mendel-Gleason
 * Copyright: Datachemist Ltd. 
 * Licence: Apache License 2.0
 */

/**********************
 * Types
 * 
 * The following types are used in the metainterpreter:
 *
 * :- type error_tree ---> error_leaf(any,atom) ; error_branch(any,atom,list(error_tree))
 * :- type maybe(T) ---> just(T) ; none.
 *
 */

/**********************
 * Primitive type predicates 
 * 
 * 
 */
isa_integer(X) :-
    integer(X).

isa_list([]).
isa_list([_|T]) :-
    isa_list(T).

isa_list([],integer).
isa_list([H|T],integer) :-
    isa_integer(H),
    isa_list(T,integer).
    
/* 
 * metainterpret(Term,MaybeError:maybe(domain_error)) is det.
 * 
 * Metainterpret/2 does not fail, but rather keeps information about 
 * why it *would* fail under normal circumstances.
 */
metainterpret(true, none).
metainterpret(\+ T, ME) :-
    (   \+ metainterpret(T,_)
    ->  ME = none
    ;   ME = just(error_leaf(\+ T,M)),
        format(atom(M), 'The negation ~q was not successful.', [\+ T])
    ).
metainterpret(isa_integer(X), ME) :-
    (   integer(X)
    ->  ME = none
    ;   ME = just(error_leaf(X, M)), 
        format(atom(M), '~q is not an integer', [X])
    ).
metainterpret(isa_atom(X), ME) :-
    (   atom(X)
    ->  ME = none
    ;   ME = just(error_leaf(X, M)), 
        format(atom(M), '~q is not an atom', [X])
    ).
metainterpret(isa(X,T), ME) :-
    % if the type variable is still a variable, we
    % need to suspend the interpretation.
    var(T),
    !,
    when(ground(T),
         metainterpret(isa(X,T),ME)).
metainterpret(isa(X,T), ME) :-
    T =.. [F|Args],
    atom_concat('isa_',F,G),
    Goal =.. [G,X|Args],
    metainterpret(Goal, ME).
metainterpret((TP1,TP2), ME) :-
    metainterpret(TP1, ME1),
    metainterpret(TP2, ME2),
    (   ME1 = none,
        ME2 = none
    ->  ME = none
    ;   ME1 = none
    ->  ME2 = just(E2),
        ME = just(error_branch(TP2, M, [E2])),
        format(atom(M), 'Right conjuct fails: ~q', TP2)
    ;   ME2 = none
    ->  ME1 = just(E1),
        ME = just(error_branch(TP1, M, [E1])),
        format(atom(M), 'Left conjuct fails: ~q', TP1)
    ;   ME1 = just(E1),
        ME2 = just(E2),
        ME = just(error_branch((TP1,TP2), M, [E1,E2])),
        format(atom(M), 'Both conjuncts fail: ~q and ~q', [TP1,TP2])
    ).
metainterpret((TP1;TP2), ME) :-
    metainterpret(TP1,ME1),
    metainterpret(TP2,ME2),
    (   ME1=just(E1),
        ME2=just(E2)
    ->  ME = just(error_branch((TP1;TP2), M, [E1,E2])),
        format(atom(M), 'No viable clauses for disjunction ~q',
               [(TP1;TP2)])
    ;   ME1=none,
        ME2=none
    ->  ME = just(error_leaf((TP1;TP2),M)),
        format(atom(M),'Too many successful clauses for disjunction ~q',
               [(TP1;TP2)])
    ;   ME=none
    ).
metainterpret((TP1=TP2), ME) :-
    (   TP1=TP2
    ->  ME=none
    ;   ME = just(error_leaf((TP1=TP2),Msg)),
        format(atom(Msg), 'Non unifiable term elements ~q and ~q', [TP1,TP2])
    ).
metainterpret(P, ME) :-
    functor(P,F,N),
    \+ member(F,[isa,isa_integer,',',';', '=', true]),
    !,
    length(Vars,N),
    P =.. [F|Args],
    Q =.. [F|Vars],
    bagof(ME_i-Body,(clause(Q, Body),
                     (   Vars = Args
                     ->  metainterpret(Body,ME_i)
                     ;   ME_i = just(error_leaf((Vars=Args),M)),
                    format(atom(M), 'Head ~q does not match arguments ~q', [Q,Args])
                     )
                    ),
          MEs),
    include([none-_]>>(true), MEs, Successes),
    maplist([_-Body,Body]>>(true), Successes, Bodies),        
    include([just(E)-_]>>(true), MEs, Just_Failures),
    maplist([just(E)-_,E]>>(true), Just_Failures, Failures),
    (   MEs = []
    ->  ME = just(error_leaf(P,M)),
        format(atom(M),'No predicate ~q defined', [F/N])
    ;   Successes = []
    ->  ME = just(error_branch(P,M,Failures)),
        format(atom(M), 'No successful clause for predicate ~q', [P])
    ;   Successes = [_,_|_]
    ->  ME = just(error_leaf(P:-Bodies, M)),
        format(atom(M), 'Too many viable clauses for predicate ~q:~n ~q',
               [P,Bodies])
    ;   ME = none
    ).

/* 
 * stacks(Error:error, Stack:list(pair(any,atom))) is nondet. 
 *
 * Finds each stack of an error.
 */
stacks(error_leaf(T,M),[T-M]).
stacks(error_branch(T,M,L),[T-M|S]) :-
    member(E,L),
    stacks(E,S).

/*  
 * deepest(Error:error,Stack:list(error)) is semidet.
 */
deepest(Error,Stack) :- 
    bagof(S-N, (stacks(Error,S), length(S,N)), Stacks),
    predsort([C,_-N1,_-N2]>>(compare(C,N1,N2)), Stacks, [Stack-_|_]).

/* 
 * write_stack(Stack:list(error))
 */
write_stack(Stack) :-
    reverse(Stack,Rev),
    forall(member(_-M,Rev),
           (   nl,
               write(M)
           )).

/* 
 * We can use the above metainterpreter to implement HM style type checking 
 * with something along the following lines. 

:- type list(T) --> [] ; [T|list(T)].

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

 */
