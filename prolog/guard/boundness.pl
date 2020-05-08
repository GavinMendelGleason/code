:- module(boundness, [
              meet/3,
              op(601, xfx, @)
          ]).

/*
 * Implementation of a complete lattice for binding status.
 */

:- use_module(complete_lattice).
:- use_module(clpad).

element(top).
element(var).
element(nonvar).
element(ground).
element(bottom).

order(var,top).
order(ground,top).
order(nonvar,ground).
order(bottom,nonvar).
order(bottom,var).

:- dynamic meet/3.
:- lattice_completion(element,order,meet).

% We need to create a couple of predicates automagically from meet
:- dynamic attr_unify_hook/2.
:- dynamic attribute_goals/1.
:- create_abstract_domain(boundness).
