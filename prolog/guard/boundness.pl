:- module(boundness, [
              meet/3,
              op(601, xfx, @)
          ]).

/*
 * Implementation of a complete lattice for binding status.
 */

:- use_module(complete_lattice).
:- use_module(library(plunit)).
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
:- dynamic join/3.
:- dynamic pseudo_compliment/3.
:- lattice_completion(element,order).

:- begin_tests(boundness).

test(meet,[]) :-
    meet(var,nonvar,bottom),
    meet(nonvar,ground,nonvar).

test(join,[]) :-
    join(nonvar,ground,nonvar),
    join(var,nonvar,top).

test(pseudo_compliment,[]) :-
    pseudo_compliment(nonvar,[var]),
    pseudo_compliment(var,[nonvar,ground]),
    pseudo_compliment(ground,[var]).

:- end_tests(boundness).

% We need to create a couple of predicates automagically from meet
:- dynamic attr_unify_hook/2.
:- dynamic attribute_goals/1.
:- create_abstract_domain(boundness).

