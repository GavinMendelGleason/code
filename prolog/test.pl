module(test,[]).

errorneous(Module,Goal) :-
    throw(determinism_error(Module:Goal,erroneous)).

failure(Module,Goal) :-
    call(Module:Goal),
    throw(determinism_error(Module:Goal,failure)).

det(Module,Goal) :-
    (   call_cleanup(Module:Goal, Det=true),
        (   Det == true
        ->  true
        ;   throw(detreminism_error(Module:Goal, det))
        )
    ->  true
    ;   throw(detreminism_error(Module:Goal, det))
    ).

semidet(Module,Goal) :-
    (   call_cleanup(Module:Goal, Det=true),
        (   Det == true
        ->  true
        ;   throw(detreminism_error(Module:Goal, semidet))
        )
    ->  true
    ;   fail
    ).
    
multi(Module,Goal) :-
    (   \+ call(Module:Goal)
    ->  throw(determinism_error(Module:Goal,multi))
    ;   call(Module:Goal)
    ).
 
nondet(Module,Goal) :-
    call(Module:Goal).
