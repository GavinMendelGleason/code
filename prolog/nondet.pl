:- module(nondet,[multi/2, multi2/2]).

multi(Module,Goal) :-
    (   \+ call(Module:Goal)
    ->  throw(determinism_error(Module:Goal,multi))
    ;   call(Module:Goal)
    ).


semidet(Module,Goal) :-
    (   call_cleanup(Module:Goal, Det=true),
        (   Det == true
        ->  true
        ;   throw(determinism_error(Module:Goal, semidet))
        )
    ->  true
    ;   fail
    ).

multi2(Module,Goal) :-
    setup_call_cleanup(
        nb_setval('__multi', not_fired),
        (   Module:Goal,
            nb_setval('__multi', fired)
        ),
        (   nb_getval('__multi', not_fired)
        ->  throw(determinism_error(Module:Goal, multi))
        ;   true
        )
    ).

    
