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
:- lattice_completion(element,order,meet).
:- dynamic attr_unify_hook/2.
:- dynamic attribute_goals/1.
:- create_abstract_domain(types).
