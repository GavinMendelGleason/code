:- module(types, [
              in/2,
              meet/3,
              pseudo_complement/2,
              op(601, xfx, @)
          ]).

/*
 * Implementation of a complete lattice for binding status.
 */

:- use_module(complete_lattice).
:- use_module(clpad).
:- reexport(clpad, [domain/2,anti_domain/2]).

element(top).
element(string).
element(atom).
element(number).
element(integer).
element(list).
element(bottom).

order(string,top).
order(atom,top).
order(number,top).
order(list,top).
order(integer,number).
order(bottom,string).
order(bottom,atom).
order(bottom,integer).
order(bottom,list).

in(_,top).
in(X,string) :-
    string(X).
in(X,atom) :-
    atom(X).
in(X,number) :-
    number(X).
in(X,integer) :-
    integer(X).
in(X,list) :-
    list(X).

:- dynamic meet/3.
:- dynamic join/3.
:- dynamic pseudo_complement/2.
:- lattice_completion(element,order).

:- begin_tests(types).

test(meet,[]) :-
    meet(atom,number,bottom),
    meet(number,integer,integer).

test(join,[]) :-
    join(atom,number,top),
    join(number,integer,number).

test(pseudo_complement,[]) :-
    pseudo_complement(integer,[string,atom,list]),
    pseudo_complement(atom,[string,number,integer,list]).

:- end_tests(types).

:- dynamic attr_unify_hook/2.
:- dynamic attribute_goals/1.
:- create_abstract_domain(types).
