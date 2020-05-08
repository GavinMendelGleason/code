:- module(types, [
              meet/3,
              domain/2,
              op(601, xfx, @)
          ]).

/*
 * Implementation of a complete lattice for binding status.
 */

:- use_module(complete_lattice).
:- use_module(clpad).
:- reexport(clpad, [domain/2]).

element(string).
element(atom).
element(number).
element(integer).
element(bottom).
element(list).

order(string,top).
order(atom,top).
order(number,top).
order(list,top).
order(integer,number).
order(bottom,string).
order(bottom,atom).
order(bottom,integer).
order(bottom,list).

:- dynamic meet/3.
:- dynamic join/3.
:- dynamic pseudo_compliment/2.
:- lattice_completion(element,order).

:- begin_tests(types).

test(meet,[]) :-
    meet(atom,number,bottom),
    meet(number,integer,integer).

test(join,[]) :-
    join(atom,number,top),
    join(number,integer,number).

test(pseudo_compliment,[]) :-
    pseudo_compliment(integer,[string,atom,list]),
    pseudo_compliment(atom,[string,number,integer,list]).

:- end_tests(types).

:- dynamic attr_unify_hook/2.
:- dynamic attribute_goals/1.
:- create_abstract_domain(types).
