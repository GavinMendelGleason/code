:- module(query, []).

:- use_module(syntax).
:- use_module(check_types).

/*
 * Module to test query ideas
 */

t(x,y,n(z)).
t(e,y,n(w)).
t(f,z,l(1))

compile_query(p(Predicate),Goal) -->
    compile_predicate(Predicate,Goal).
compile_query((Q1,Q2),Goal) -->
    compile_query(Q1,Goal1),
    compile_query(Q1,Goal2).
compile_query((Q1;Q2),Goal) -->
    peek(S0),
    compile_query(Q1,Goal1),
    peek(S1),
    return(S0),
    compile_query(Q2,Goal2),
    merge(S1).

compile_predicate(Predicate, Goal) :-
    Predicate = [P|Args],
    length(Args,N),
    compile_predicate_descriptor(P/N,Args,Goal).

is_true(true).

compile_predicate_descriptor(P/N,Args,Goal) -->
    { query_term_properties(P/N,System_P,Modes,Types) },
    mapm(resolve,Args,Resolved,Modes,Types,Pre_Goals,Post_Goals),
    { Predicate_Goal =.. [System_P|Resolved],
      append([Pre_Goals,[Predicate_Goal],Post_Goals], Goal_List),
      exclude(is_true,Goal_List,Filtered_Goal_List),
      xfy_list(',',Goal, Filtered_Goal_List) }.

query_term_properties(t/4,[any,any,any,ground],[node,node,object,resource]).
query_term_properties(i/4,[any,any,any,ground],[node,node,object,resource]).

mode_check(ground,v(Var),Term,
           (do_or_die(
                ground(Term),
                error(instantiation_error(Var,Term))))).
mode_check(any,v(Var),_,true).
mode_check(_,n(_),_,true).
mode_check(_,n(_),_,true).

variable_resolve(Var_Name,Var) -->
    lookup_or_extend(Var_Name,Variable).

string_resolve(v(Var_Name),Variable) -->
    variable_resolve(V_Name,Variable)

language_resolve(v(Var_Name),Variable) -->
    variable_resolve(Var_Name,Variable).
language_resolve(o(Atom),Atom).

literal_resolve(v(Var_Name),Variable) -->
    variable_resolve(V,Variable).
literal_resolve(o(Atom),Atom).

term_resolve(v(Var_Name), Variable) -->
    variable_resolve(Var_Name,Variable).
term_resolve(X@L, XS@LE) -->
    string_resolve(X,XS),
    language_resolve(L,LE).
term_resolve(X^^T, XE^^TE) -->
    literal_resolve(X,XS),
    language_resolve(L,LE).
term_resolve(n(Uri), n(Uri)).

resolve(Element,Mode,Type,Pre_Goal,Post_Goal) -->
    term_resolve(Element,Term),
    mode_check(Mode,Element,Mode_Goal),
    true.
