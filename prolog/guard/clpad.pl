:- module(clpad, [
              create_abstract_domain/1,
              domain/2,
              anti_domain/2,
              op(601, xfx, @)
           ]).

:- op(601, xfx, @).

/**
 * Create a contraint system over an abstract interpretation domain
 * supplied as a module + meet/3 + psuedo_complement/2
 */

:- dynamic domain/2.
:- multifile domain/2.

:- dynamic anti_domain/2.
:- multifile anti_domain/2.

check_module_exports(Module) :-
    module_property(Module,exports(Exports)),
    memberchk(in/2,Exports),
    memberchk(meet/3,Exports),
    memberchk(pseudo_complement/2,Exports),
    !.
check_module_exports(_) :-
    throw(domain_error(
              'You need to have in/2, meet/3, pseudo_complement/2 to establish an abstract domain')).


% NOTE: We might want to think about abstracting top/bottom
%
create_abstract_domain(Module) :-
    check_module_exports(Module),
    retractall(clpad:anti_domain(_,_@Module)),
    retractall(clpad:domain(_,_@Module)),
    retractall(Module:attr_unify_hook/2),
    retractall(Module:atribute_goals/2),
    % Add domain predicates for this module
    assertz(
        (domain(X, Domain@Module) :-
             nonvar(X),
             !,
             Module:in(X, Domain))),
    assertz(
        (domain(X, Domain@Module) :-
             var(Domain),
             !,
             get_attr(X, Module, Domain))),
    assertz(
        (domain(X, Domain@Module) :-
             put_attr(Y, Module, Domain),
             X = Y)),
    % Add anti_comain predicates for this module
    assertz(
        (anti_domain(X, Domain@Module) :-
             nonvar(X),
             !,
             \+ Module:in(X,Domain))),
    assertz(
        (anti_domain(X, Domain@Module) :-
             Module:pseudo_complement(Domain,Anti_Domains),
             member(Anti_Domain, Anti_Domains),
             put_attr(Y, Module, Anti_Domain),
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
