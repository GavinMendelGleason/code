:- module(guard_testing, [
              abs/2
          ]).

:- use_module(guard).

abs(X,Y) :-
    X >= 0
    | X = Y.
abs(X,Y) :-
    X < 0
    | Y is -X.

my_pred(a,X,Y) :-
    X > 0
    | Y is 13 / X.
my_pred(b,X,Y) :-
    true
    | Y is 13 / X.

% This works, but makes terrible complaints.
%
% unsafe(X,Y) :-
%     X > 0
%     | Y is 10.
% unsafe(X,Y) :-
%     true
%     | X = Y.

/*
 * Example from terminus!
 */
:- op(601, xfx, ^^).
:- op(601, xfx, @).
nonvar_literal(Atom@Lang, Literal) :-
    atom(Atom)
    | atom_string(Atom, String),
      nonvar_literal(String@Lang, Literal).
nonvar_literal(Atom^^Type, Literal) :-
    atom(Atom)
    | atom_string(Atom, String),
      nonvar_literal(String^^Type, Literal).
nonvar_literal(String@Lang, value(S)) :-
    string(String),
    nonvar(Lang)
    | format(string(S), '~q@~q', [String,Lang]).
nonvar_literal(Val^^Type, value(S)) :-
    string(Val),
    nonvar(Type)
    | (   Type = 'http://www.w3.org/2001/XMLSchema#dateTime',
          Val = date(_Y, _M, _D, _HH, _MM, _SS, _Z, _ZH, _ZM)
      ->  date_string(Val,Date_String),
          format(string(S), '~q^^~q', [Date_String,Type])
      ;   format(string(S), '~q^^~q', [Val,Type])).
nonvar_literal(Val^^Type, _) :-
    \+ atom(Val),
    (   var(Val)
    ;   var(Type))
    | true.
nonvar_literal(Val@Lang, _) :-
    \+ atom(Val),
    (   var(Val)
    ;   var(Lang))
    | true.
nonvar_literal(O, node(S)) :-
    (   atom(O)
    ;   string(O))
    | atom_string(O,S).
