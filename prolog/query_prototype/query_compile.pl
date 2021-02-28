:- module(query_compile, [
              resolve//3,
              op(601, xfx, @),
              op(601, xfx, ^^)
          ]).

:- use_module(utils).
:- use_module(dict_state).
:- use_module(check_types).

:- op(601, xfx, @).
:- op(601, xfx, ^^).

/*
 *
 */
is_var_binding(var_binding{
                   woql_var : WOQL_Var,
                   var_name : Var_Name
                   descriptor_id_difference_list : DID_DL
               }) :-
    atom(Var_Name),
    var(WOQL_Var),
    difference_list(DID_DL).
is_var_binding(prolog_var_binding{
                   woql_var : WOQL_Var,
                   var_name : Var_Name
               }) :-
    
var_record_pl_var(Var_Name,Binding,WOQL_Var) :-
    var_binding{
        woql_var : WOQL_Var,
        var_name : Var_Name
    } :< Binding.

var_compare(Op, Left, Right) :-
    compare(Op, Left.var_name, Right.var_name).

merge_states(S0) -->
    { B0 = (S0.get(bindings)),
      R0 = (S0.get(resources)) },

    view(bindings,B1),
    view(resources,R1),

    { merge_output_bindings(B0,B1,Bindings),
      merge_resource_bindings(R0,R1,Resources) },

    put(bindings,Bindings),
    put(resources,Resources).

merge_vars(Var1,Var2) :-
    var_binding{
        woql_var : WOQL_Var1,
        var_name : Var_Name1
    } :< Var1,
    var_binding{
        woql_var : WOQL_Var2,
        var_name : Var_Name2
    } :< Var2,

    (   get_dict(

unify_same_named_vars([],_Var).
unify_same_named_vars([Var1|Vars],Var) :-
    (   var_compare((=), Var, Var1)
    ->  merge_vars(Var,Var1)
    ;   true),
    unify_same_named_vars(Vars,Var).

unify_output_bindings([], _).
unify_output_bindings([Var|Vars], Bindings) :-
    unify_same_named_vars(Bindings,Var),
    unify_output_bindings(Vars, Bindings).

merge_output_bindings(B0, B1, Bindings) :-
    unify_output_bindings(B0,B1),
    append(B0, B1, All),
    predsort(var_compare, All, Bindings).

unify_identical_resource([], _).
unify_identical_resource([Resource|Resources], Resource1) :-
    ignore(Resource = Resource1),
    unify_identical_resource(Resources, Resource1).

unify_resource_bindings([], _).
unify_resource_bindings([Resource|Resources], Resources1) :-
    unify_identical_resource(Resources1,Resource),
    unify_resource_bindings(Resources,Resources1).

merge_resource_bindings(B0, B1, Bindings) :-
    unify_resource_bindings(B0, B1),
    append(B0, B1, All),
    predsort(compare, All, Bindings).

/*
 * Module to test query ideas
 */

compile_goal(p(Predicate),Goal) -->
    compile_predicate(Predicate,Goal).
compile_goal((Q1,Q2),(Goal1,Goal2)) -->
    compile_goal(Q1,Goal1),
    compile_goal(Q2,Goal2).
compile_goal((Q1;Q2),(Goal1;Goal2)) -->
    peek(S0),
    compile_goal(Q1,Goal1),
    peek(S1),
    return(S0),
    compile_goal(Q2,Goal2),
    merge_states(S1).

compile_predicate(Predicate, Goal) -->
    { Predicate =.. [P|Args],
      length(Args,N) },
    compile_predicate_descriptor(P/N,Args,Goal).

is_true(true).

compile_predicate_descriptor(P/N,Args,Goal) -->
    { query_term_properties(P{ arity: N,
                               implementation: System_P,
                               mode: Modes,
                               type: Types,
                               resource: Resource,
                               stream: Stream}),
      zip(Args,Resolved,Args_Resolved),
      zip(Modes,Types,Modes_Types) },
    mapm(resolve,Args_Resolved,Modes_Types,Pre_Goals_Post_Goals),
    resource_arg(Resource,Types,Args,Resource_Arg),
    stream_arg(Stream,Stream_Arg),
    { zip(Pre_Goals, Post_Goals, Pre_Goals_Post_Goals),
      append([Resolved,Resource_Arg,Stream_Arg],Implementation_Args),
      Predicate_Goal =.. [System_P|Implementation_Args],
      append([Pre_Goals,[Predicate_Goal],Post_Goals], Goal_List),
      xfy_list(',',Goal, Goal_List) }.

%% resource_arg(true, Args, Types, Resource_Arg) -->
%%     {convlist([Arg,resource,Arg]>>true, Args, Types, Resource_Arg)}

%% stream_arg(Stream, Args, Types, Stream_Arg) -->
%%     peek(Stream, Arg


query_term_properties(
    t{ arity: 3,
       implementation: triple,
       mode: [any,any,any],
       type: [node,node,obj],
       resource: true,
       stream: false }).
query_term_properties(
    t{ arity: 4,
       implementation: triple,
       mode: [any,any,any,ground],
       type: [node,node,obj,resource],
       resource: true,
       stream: false }).
query_term_properties(
    insert{ arity: 3,
       implementation: insert,
       mode: [any,any,any],
       type: [node,node,obj],
       resource: true,
       stream: false }).
query_term_properties(
    insert{ arity: 4,
       implementation: insert,
       mode: [any,any,any,ground],
       type: [node,node,obj,resource],
       resource: true,
       stream: false }).

mode_check_var(ground,Var,Term,
               (do_or_die(
                    ground(Term),
                    error(instantiation_error(Var,Term))))).
mode_check_var(any,_,_,true).

mode_check(v(Var),Type,Term,Goal) :-
    mode_check_var(Type,Var,Term,Goal).
mode_check(n(_),_,_,true).
mode_check(l(_),_,_,true).
mode_check(o(_),_,_,true).
mode_check(r(_),_,_,true).

type_check_node(node).
type_check_node(obj).

type_check_literal(literal).
type_check_literal(obj).

type_check(r(Term), resource, _, true) :-
    % Must be atom at compile time.
    do_or_die(
        the(atom,Term),
        error(woql_type_error(Term,resource))).
type_check(v(_), Type, Term, will_be(Type,Term)).
type_check(n(_), Type, _, true) :-
    type_check_node(Type).
type_check(l(_), Type, _, true) :-
    type_check_literal(Type).

lookup(Var_Name,Prolog_Var,[Record|_B0]) :-
    var_record_pl_var(Var_Name,Record,Prolog_Var),
    !.
lookup(Var_Name,Prolog_Var,[_Record|B0]) :-
    lookup(Var_Name,Prolog_Var,B0).

extend(Var_Name, Prolog_Var, B0,
       [var_binding{
           woql_var : Prolog_Var,
           var_name : Var_Name}
       |B0]).

lookup_or_extend(Var_Name, Prolog_Var) -->
    update(bindings,B0,B1),
    {
        (   lookup(Var_Name, Prolog_Var, B0)
        ->  B0 = B1
        ;   extend(Var_Name, Prolog_Var, B0, B1)
    }.

variable_resolve(Var_Name,Variable) -->
    lookup_or_extend(Var_Name,Variable).

type_resolve(v(Var_Name), Variable, true) -->
    variable_resolve(Var_Name,Variable).
type_resolve(type(Type), Result, Goal) -->
    { Goal = basetype_subsumption_of(Type, Result) }.

language_resolve(v(Var_Name),Variable) -->
    variable_resolve(Var_Name,Variable).
language_resolve(lang(String),String)  --> {true}.

base_literal_resolve(v(Var_Name),Variable) -->
    variable_resolve(Var_Name,Variable).
base_literal_resolve(base(String),String) --> {true}.

register_resource(Uri, Var) -->
    update(resources,Old,New),
    { (   memberchk(Uri=Var, Old)
      ->  Old = New
      ;   New = [Uri=Var|Old])
    }.

literal_resolve(X@L, XS@LE, true) -->
    base_literal_resolve(X, XS),
    language_resolve(L, LE).
literal_resolve(X^^T, XE^^TE, Goal) -->
    base_literal_resolve(X,XE),
    type_resolve(T, TE, Goal).

term_resolve(v(Var_Name), Variable, true) -->
    variable_resolve(Var_Name, Variable).
term_resolve(l(Literal), Variable, Goal) -->
    literal_resolve(Literal,Variable,Goal).
term_resolve(r(Uri), Var, true) -->
    register_resource(Uri, Var).
term_resolve(n(Uri), n(Uri), true) -->
    { true }.


resolve(Element-Term,Mode-Type,(Mode_Goal,Type_Goal,Term_Goal)-true) -->
    term_resolve(Element,Term,Term_Goal),
    { mode_check(Element,Mode,Term,Mode_Goal),
      do_or_die(
          type_check(Element,Type,Term,Type_Goal),
          error(woql_type_error(Element,Term,Type)))
    }.

simplify(true,true) :-
    !.
simplify((A,B),C) :-
    !,
    simplify(A,A1),
    simplify(B,B1),
    (   A1 = true
    ->  B1 = C
    ;   B1 = true
    ->  A1 = C
    ;   C = (A1,B1)).
simplify((A;B),C) :-
    !,
    simplify(A,A1),
    simplify(B,B1),
    (   A1 = true
    ->  B1 = C
    ;   B1 = true
    ->  A1 = C
    ;   C = (A1;B1)).
simplify(G,G).

search_([H|T],Term) :-
    (   Term == H
    ->  true
    ;   search_(T,Term)).

search(Term,List) :-
    search_(List,Term).

goal_optimised((Goal1,Goal2), (DeDup1,DeDup2)) -->
    !,
    goal_optimised(Goal1, DeDup1),
    goal_optimised(Goal2, DeDup2).
goal_optimised((Goal1;Goal2), (DeDup1;DeDup2)) -->
    !,
    peek(S0), % Need to follow the same conjunction trace
    goal_optimised(Goal1, DeDup1),
    return(S0),
    goal_optimised(Goal2, DeDup2).
goal_optimised(Goal, true) -->
    peek(Dups),
    { search(Goal,Dups) },
    !.
goal_optimised(Goal, Goal) -->
    peek(Dups),
    return([Goal|Dups]).

goal_optimised(Goal,DeDup) :-
    goal_optimised(Goal, DeDup, [], _).

compile_query(Ast,Result,In,Out) :-
    once(run(compile_goal(Ast, Goal),
             In,
             Out)),
    goal_optimised(Goal,DeDup),
    simplify(DeDup, Result).

compile_query(Ast,Goal,Result) :-
    compile_query(Ast,Goal,
                  state{
                      bindings : [],
                      resources : []
                  },
                  Result).

:- begin_tests(compile).
:- thread_local t/3.
:- thread_local t/4.

test(compile_triple, []) :-

    Term = p(t(v('X'),v('Y'),v('Z'))),

    compile_query(Term,Goal,_),
    Goal = (
        will_be(node,A),
        will_be(node,B),
        will_be(obj,C),
        t(A,B,C)
    ).

test(compile_two_triples, []) :-

    Term = (p(t(v('X'),v('Y'),v('Z'))),
            p(t(n(x),v('Y'),n(z)))),

    compile_query(Term,Goal,_),

    Goal = (
        (will_be(node,X),
         will_be(node,Y),
         will_be(obj,Z),
         t(X,Y,Z)
        ),
        t(n(x),Y,n(z))
    ).


test(search_triples, [
         setup((assertz(t(n(x),n(y),n(z))),
                assertz(t(n(e),n(y),n(w))),
                assertz(t(n(f),n(z),l(base("1")^^type(xsd_string)))))),
         cleanup(retractall(t(_,_,_)))
     ]) :-
    Term = (p(t(v('X'),v('Y'),v('Z'))),
            p(t(n(x),v('Y'),n(z)))),

    compile_query(Term,Goal,Result),
    Template = (Result.bindings),

    findall(Template,
            Goal,
            Bindings),

    maplist([Binding,Value]>>(lookup('X', Value, Binding)), Bindings, Xs),
    sort(Xs,[n(e),n(x)]),

    maplist([Binding,Value]>>(lookup('Y', Value, Binding)), Bindings, Ys),
    sort(Ys,[n(y)]),

    maplist([Binding,Value]>>(lookup('Z', Value, Binding)), Bindings, Zs),
    sort(Zs,[n(w),n(z)]).


test(extend_resources, [
         setup((assertz(t(n(x),n(y),n(z), r('my/database'))),
                assertz(t(n(e),n(y),n(w))),
                assertz(t(n(f),n(z),l(base("1")^^type(xsd_string)))))),
         cleanup((retractall(t(_,_,_)),
                  retractall(t(_,_,_,_))
                 ))
     ]) :-

    Term = (p(t(v('X'),v('Y'),v('Z'), r('my/database'))),
            p(t(v('Q'),v('Z'),v('Lit')))),

    compile_query(Term,Goal,Result),

    Goal = ((will_be(node,X),
             will_be(node,Y),
             will_be(obj,Z),
             t(X,Y,Z,R)),
            will_be(node,Q),
            will_be(node,Z),
            will_be(obj,Lit),
            t(Q,Z,Lit)),

    Result_Bindings = (Result.bindings),
    sort(Result_Bindings,Template),
    findall(Template,
            Goal,
            Bindings),
    Bindings = [[var_binding{var_name:'X',woql_var:n(x)},
                 var_binding{var_name:'Y',woql_var:n(y)},
                 var_binding{var_name:'Z',woql_var:n(z)},
                 var_binding{var_name:'Q',woql_var:n(f)},
                 var_binding{var_name:'Lit',woql_var:l(base("1")^^type(xsd_string))}]],
    % Check resources
    Resources = (Result.resources),
    R = 1,
    memberchk('my/database'=Resource_Var,Resources),
    ground(Resource_Var),
    Resource_Var = 1.


test(disjunction_resource_tests, [
         setup((assertz(t(n(x),n(y),n(z), r('my/database'))),
                assertz(t(n(e),n(y),n(w))),
                assertz(t(n(f),n(z),l(base("1")^^type(xsd_string)), r('my/database'))))),
         cleanup((retractall(t(_,_,_)),
                  retractall(t(_,_,_,_))
                 ))
     ]) :-

    Term = (   p(t(v('X'),v('Y'),n(z), r('my/database')))
           ;   p(t(v('X'),v('Y'),l(base("1")^^type(xsd_string)), r('my/database')))),

    compile_query(Term,Goal,Result),
    writeq(Goal),
    Goal =
    (   will_be(node,X),
        will_be(node,Y),
        t(X,Y,n(z),R1)
    ;   will_be(node,X),
        will_be(node,Y),
        basetype_subsumption_of(xsd_string,Type),
        t(X,Y,"1"^^Type,R2)),


    Resources = (Result.resources),

    memberchk('my/database'=Resource_Var,Resources),
    Resource_Var = 42,
    R1 == 42,
    R2 == 42.

:- end_tests(compile).

