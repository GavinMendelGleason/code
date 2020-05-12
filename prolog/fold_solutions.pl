:- module(fold_solutions,
	      [sfoldr/4,
           val/1
	      ]).

val(1). 
val(2).
val(3).

:- meta_predicate sfoldr(3,1,+,-).
sfoldr(P,Gen,Z,R) :-
    !,
    State = state(Z),
    (  call(Gen,X), 
       arg(1, State, M),
       call(P,X,M,R),
       nb_setarg(1, State, R),
       fail
    ;  arg(1, State, R),
       nonvar(R)
    ).
