:- module(complete_lattice, [
              lattice_completion/2
          ]).

:- meta_predicate le(?,?,1,2).
le(X,X,Element,_Order) :-
    call(Element,X).
le(X,Y,_Element,Order) :-
    call(Order,X,Y).
le(X,Z,Element,Order) :-
    call(Order,X,Y),
    le(Y,Z,Element,Order).

glb(X,Y,GLB,Element,Order) :-
    le(GLB,X,Element,Order),
    le(GLB,Y,Element,Order),
    !.

lub(X,Y,LUB,Element,Order) :-
    le(X,LUB,Element,Order),
    le(Y,LUB,Element,Order),
    !.

:- meta_predicate lattice_completion(1,2).
lattice_completion(Element,Order) :-
    strip_module(Element, Module, _),
    retractall(Module:meet(_,_,_)),
    retractall(Module:join(_,_,_)),
    retractall(Module:pseudo_complement(_,_)),

    forall(
        (   call(Element,Elt_A),
            call(Element,Elt_B),
            glb(Elt_A,Elt_B,Elt,Element,Order)
        ),
        assertz(Module:meet(Elt_A,Elt_B,Elt))
    ),

    forall(
        (   call(Element,Elt_A),
            call(Element,Elt_B),
            lub(Elt_A,Elt_B,Elt,Element,Order)
        ),
        assertz(Module:join(Elt_A,Elt_B,Elt))
    ),

    forall(
        call(Element,Elt_A),
        (   findall(Complement,
                    (   call(Element,Complement),
                        \+ memberchk(Complement, [top,bottom]),
                        Module:meet(Elt_A,Complement,bottom),
                        Module:join(Elt_A,Complement,top)
                    ),
                    Complements),
            assertz(Module:pseudo_complement(Elt_A,Complements))
        )
    ).

