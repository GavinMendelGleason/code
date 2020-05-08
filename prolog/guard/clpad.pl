:- module(clpad, [
              create_abstract_domain/1,
              domain/2,
              op(601, xfx, @)
           ]).

:- op(601, xfx, @).

/**
 * Create a contraint system over an abstract interpretation domain
 * supplied as a module + meet/3
 */

:- dynamic domain/2.
:- multifile domain/2.

% NOTE: We might want to think about abstracting top/bottom
%
create_abstract_domain(Module) :-
    retractall(clpad:domain(_,_@Module)),
    retractall(Module:attr_unify_hook/2),
    retractall(Module:atribute_goals/2),
    % Add domain predicates for this module
    assertz(
        (domain(X, Domain@Module) :-
             var(Domain),
             !,
             get_attr(X, Module, Domain))),
    assertz(
        (domain(X, Domain@Module) :-
             put_attr(Y, Module, Domain),
             X = Y)),
    % Create the attribution hooks for the abstract domain
    assertz(
        %  An attributed variable with attribute value Domain has been
        %  assigned the value Y
        Module:(attr_unify_hook(Domain, Y) :-
                    (   get_attr(Y, Module, Domain2)
                    ->  call(Module:meet(Domain, Domain2, NewDomain)),
                        (   NewDomain == bottom
                        ->  fail
                        ;   put_attr(Y, Module, NewDomain)
                        )
                    ;   var(Y)
                    ->  put_attr(Y, Module, Domain)
                    ;   put_attr(Y, Module, top)
                    ))),

    % Expand DCG form
    expand_term(
        (attribute_goals(X) -->
             { get_attr(X, Module, Domain) },
             [ clpad:domain(X, Domain@Module) ]),
        Attribute_Goals),
    %  Translate attributes from this module to residual goals
    assertz(Module:Attribute_Goals).
