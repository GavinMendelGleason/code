:- module(meta_tests,[]).

:- use_module(regular).
:- use_module(check_types).

wf_literal_lang(en).

wf_literal_base(o(X)) :-
    the(atom,X).
wf_literal_base(v(X)) :-
    the(atom,X).

wf_literal_type(o(X)) :-
    the(atom,X).
wf_literal_type(v(X)) :-
    the(atom,X).

wf_resource(X) :-
    the(atom,X).

wf_literal(v(X)) :-
    the(atom,X).
wf_literal('^^'(X,T)) :-
    wf_literal_base(X),
    wf_literal_type(T).
wf_literal('@'(X,L)) :-
    wf_literal_base(X),
    wf_literal_lang(L).

wf_node(v(X)) :-
    the(atom,X).
wf_node(n(X)) :-
    the(atom,X).

wf_object(no(X)) :-
    wf_node(X).
wf_object(lo(X)) :-
    wf_literal(X).

wf_p(t(X,Y,Z)) :-
    wf_node(X),
    wf_node(Y),
    wf_object(Z).
wf_p(i(X,Y,Z,G)) :-
    wf_node(X),
    wf_node(Y),
    wf_object(Z),
    wf_resource(G).

wf((A,B)) :- wf(A), wf(B).
wf((A;B)) :- wf(A), wf(B).
wf(p(P)) :- wf_p(P).

:- begin_tests(mi).
:- use_module(regular).

test(node,[]) :-
    Term = meta_tests:v('X'),
    mi(wf_node(Term), [], Term).

test(two_triples,[]) :-
    Term = meta_tests:(t(v('X'),v('Y'),no(v('Z'))),
                       t(n(a),v('Y'),lo(v('Z')))),
    mi(wf(Term), [], Term).

:- end_tests(mi).
