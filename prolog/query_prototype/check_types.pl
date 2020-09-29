:- module(check_types, [can_be/2,
                        will_be/2,
                        the/2,
                        node/1,
                        literal/1,
                        obj/1]).

:- op(601, xfx, @).
:- op(601, xfx, ^^).

:- meta_predicate do_or_die(:,?).
do_or_die(Goal, Error) :-
    (   call(Goal)
    ->  true
    ;   throw(Error)).

will_be(Type,X) :-
    freeze(X,
           do_or_die(
               the(Type,X),
               error(type_error(Type,X),_Ctx))).

can_be(_Type,X) :-
    var(X),
    !.
can_be(Type,X) :-
    the(Type,X).

is_already(_Type,X) :-
    var(X),
    !,
    throw(error(instantiation_error,_Ctx)).
is_already(Type,X) :-
    the(Type,X).

the(literal,X) :-
    literal(X).
the(obj,X) :-
    obj(X).
the(node,X) :-
    node(X).
the(ground,X) :-
    ground(X).
the(var,X) :-
    var(X).
the(atom,X) :-
    atom(X).
the(string,X) :-
    string(X).
the(integer,X) :-
    integer(X).
the(any,_X).

node(n(X)) :-
    can_be(atom,X).

literal_base(v(X)) :- atom(X).
literal_base(base(X)) :-
    can_be(string,X).

literal_type(v(X)) :- atom(X).
literal_type(type(X)) :-
    can_be(atom,X).

literal(v(X)) :- atom(X).
literal(l(X^^Y)) :-
    literal_base(X),
    literal_type(Y).

obj(v(X)) :- can_be(atom,X).
obj(n(X)) :- can_be(atom,X).
obj(l(X)) :- can_be(literal,l(X)).
