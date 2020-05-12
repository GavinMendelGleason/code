:- module(boundness, [
              in/2,
              meet/3,
              pseudo_complement/2,
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
order(nonvar,top).
order(ground,nonvar).
order(bottom,ground).
order(bottom,var).

in(_,top).
in(X,var) :-
    var(X).
in(X,nonvar) :-
    nonvar(X).
in(X,ground) :-
    ground(X).

:- dynamic meet/3.
:- dynamic join/3.
:- dynamic pseudo_complement/3.
:- lattice_completion(element,order).

:- begin_tests(boundness).

test(meet,[]) :-
    meet(var,nonvar,bottom),
    meet(nonvar,ground,ground).

test(join,[]) :-
    join(nonvar,ground,nonvar),
    join(var,nonvar,top).

test(pseudo_complement,[]) :-
    pseudo_complement(nonvar,[var]),
    pseudo_complement(var,[nonvar,ground]),
    pseudo_complement(ground,[var]).

:- end_tests(boundness).

% We need to create a couple of predicates automagically from meet
:- dynamic attr_unify_hook/2.
:- dynamic attribute_goals/1.
:- create_abstract_domain(boundness).
