:- module(check_types, [can_be/2,
                        is/2,
                        node/1,
                        literal/1,
                        object/1]).

can_be(Type,X) :-
    var(X),
    !.
can_be(Type,X) :-
    is(Type,X).

is(literal,X) :-
    literal(X).
is(object,X) :-
    object(X).
is(node,X) :-
    node(X).
is(ground,X) :-
    ground(X).
is(var,X) :-
    var(X).
is(atom,X) :-
    atom(X).
is(integer,X) :-
    integer(X).
is(any,_X).

node(X) :-
    can_be(atom,X).

literal(X) :-
    can_be(integer,X)

object(n(X)) :-
    node(X).
object(l(X)) :-
    node(X).

