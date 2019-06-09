:- module(mic,[]).

/* <module> Metainterpertation critic 
 * 
 * Gives us some information as to causes of failure for a restricted subset of 
 * prolog in which ';' is interpreted as exclusive disjunction.
 * 
 * This predicate is useful for creating either an ad-hoc type-checker which 
 * verifies syntax of a term (well-formedness conditions etc.) or for creating 
 * a full fledged type checker. 
 *
 * Author: Gavin Mendel-Gleason
 * Copyright: Datachemist Ltd. 
 * Licence: Apache 
 */

%:- type list(T) --> [] ; [T|list(T)].

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
 * type domain_error ---> domain_error(any,atom).
 * type maybe(T) ---> just(T) ; none.
 */
[poiutre  
/* 
 * metainterpret(Term,MaybeError:maybe(domain_error)) is det.
 * 
 * Metainterpret/2 does not fail, but rather keeps information about 
 * why it *would* fail under normal circumstances.
 */
metainterpret(\+ T, ME) :-
    (   \+ metainterpet(T,ME1)
    ->  ME = none
    ;   ME = just(domain_error(T,M)),
        format(atom(M), ' ', [])
    ).
metainterpret(isa_integer(X), ME) :-
    (   integer(X)
    ->  ME = none
    ;   ME = just(domain_error(X, M)), 
        format(atom(M), '~q is not an integer', [X])
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
    (   ME1 = just(_)
    ->  ME = ME1
    ;   metainterpret(TP2, ME)
    ).
metainterpret((TP1;TP2), ME) :-
    metainterpret(TP1,ME1),
    metainterpret(TP2,ME2),
    (   ME1=just(_),
        ME2=just(_)
    ->  ME = just(domain_error((TP1;TP2), M)),
        format(atom(M), 'No viable clauses for disjunction ~q',
               [(TP1;TP2)])
    ;   ME1=none,
        ME2=none
    ->  ME = just(domain_error((TP1;TP2),M)),
        format(atom(M),'Too many successful clauses for disjunction ~q',
               [(TP1;TP2)])
    ;   ME=none
    ).
metainterpret((TP1=TP2), ME) :-
    (   TP1=TP2
    ->  ME=none
    ;   ME = just(domain_error((TP1=TP2),Msg)),
        format(atom(Msg), 'Non unifiable term elements ~q and ~q', [TP1,TP2])
    ).
metainterpret(P, ME) :-
    functor(P,F,N),
    \+ member(F,[isa,isa_integer,',',';', '=']),
    !,
    length(Vars,N),
    P =.. [F|Args],
    Q =.. [F|Vars],
    bagof(ME_i-Body,(clause(Q, Body),
                     (   Vars = Args
                     ->  metainterpret(Body,ME_i)
                     ;   ME = just(domain_error((Vars=Args),M)),
                         format(atom(M), 'Head ~q does not match args ~q', [Q,Args])
                     )
                    ),
          MEs),
    include([none-_Body]>>(true), MEs, Results),
    (   Results = []
    ->  ME = just(domain_error(P, M)),
        format(atom(M), 'No successful clause for predicate ~q', [P])
    ;   Results = [_,_|_]
    ->  ME = just(domain_error(P, M)),
        maplist([_-Body,Body]>>(true), Results, Bodies),
        format(atom(M), 'Too many viable clauses for predicate ~q:~n ~q',
               [P,Bodies])
    ;   ME = none
    ).
