:- module(example,
          [ isa/2                    % Var, ?Domain
          ]).
:- use_module(library(ordsets)).

map(1,a).
map(2,b).
map(3,c).


isa(X,Y) :-
    var(Y), !,
    get_attr(X, isa, Y).
isa(X,Elt) :-
    atom(Elt),
    map(A,Elt),
    put_attr(Y, isa, A),
    X = Y.
isa(X,Elt) :-
    number(Elt),
    put_attr(Y, isa, Elt),
    X = Y.
    
resolve(Y) :-
    get_attr(Y, isa, Elt),
    map(Elt,Name),
    Y = Name.

%       An attributed variable with attribute value Domain has been
%       assigned the value Y

isa:attr_unify_hook(Elt, Y) :-
        (   get_attr(Y, isa, Elt2)
        ->  Elt = Elt2            
        ;   var(Y)
        ->  put_attr( Y, isa, Elt )
        ;   true
        ).

%       Translate attributes from this module to residual goals

attribute_goals(X) -->
        { get_attr(X, isa, Elt) },
        [ isa(X, Elt) ].
