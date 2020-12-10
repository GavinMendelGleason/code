:- module(ik2tree, [
              dkw/3,
              decimal_kary/3,
              kd/3,
              kary_decimal/3
          ]).

/*
 * Interleaved K^2 tree
 *
 * Interleaved K^2 trees are efficient methods of storing
 * ternary relationships
 *
 *
 */

:- use_module(library(clpfd)).

/*
 * k2 tree and persistent k2 tree prototypes
 */
/* How does this not exist? in ISO? */
log(N,B,0) :-
    B #> N.
log(N,B,Ans) :-
    N1 #= N // B,
    N1 #> 0,
    log(N1, B, A),
    Ans #= A + 1.

decimal_kary_word(Int,K,Word,WS) :-
    decimal_kary(Int,K,Rep),
    zero_pad(Rep,WS,Word).

% just short-hand
dkw(Int,K,WS) :-
    decimal_kary(Int,K,WS).

decimal_kary(Int,K,Rep) :-
    log(Int,K,R),
    decimal_kary_aux(Int,K,R,Rep).

decimal_kary(Int,K,N,Word) :-
    log(N,K,R),
    decimal_kary_aux(Int,K,R,Word).

decimal_kary_aux(Int, _, 0, [Int]).
decimal_kary_aux(Int, K, R,[D|Rep]) :-
    Int #>= 0, R #>= 0,
    P is K ** R,
    D #= Int // P,
    Rem #= Int - D * P,
    R1 #= R - 1,
    decimal_kary_aux(Rem,K,R1,Rep).

kary_decimal(W,K,N) :-
    length(W,WS),
    Exp #= WS - 1,
    kary_decimal_aux(W,K,N,Exp).

% just shorthand
kd(W,K,N) :-
    kary_decimal(W,K,N).

kary_decimal_aux([],_,0,-1).
kary_decimal_aux([A|R],K,M,Exp) :-
    New_Exp #= Exp - 1,
    kary_decimal_aux(R,K,N,New_Exp),
    Order is (K ** Exp),
    M #= N + A * Order.

zeros(0,[]).
zeros(N, [0|R]) :-
    N #> 0,
    M #= N - 1,
    zeros(M,R).

zero_pad(L,WS,Word) :-
    length(L,R),
    R #=< WS,
    P #= WS - R,
    zeros(P, Top),
    append(Top,L,Word).

empty_ik2_tree(I,K,N,Tree) :-
    Tree =
    ik2_tree{
        n : N,
        k : K,
        i : I,
        l : [],
        t : []
    }.

prefix(_, 0, []).
prefix([X|T], N, [X|L]) :-
    N #> 0,
    M #= N - 1,
    prefix(T, M, L).

prefix_or_zeros(T,Size,Level) :-
    length(T,Length),
    (   Length =< Size
    ->  zero_pad(T,Size,Level)
    ;   prefix(T,Size,Level)
    ).

:- meta_predicate assuming(0).
assuming(G) :-
    (   G
    ->  true
    ;   throw(error(assertion_failed(G)))).

create_dictionaries(Triples,Dictionaries) :-
    maplist([t(X,Y,Z),X,Y,Z]>>true,Triples, Subjects, Predicates, Objects),
    include([value(V)]>>true, Objects, Values),
    include([node(N)]>>true, Objects, Nodes),
    append(Subjects, Nodes, All_Nodes),
    sort(All_Nodes,Sorted_Nodes),
    sort(Predicates,Sorted_Predicates),
    sort(Values,Sorted_Values),
    length(Sorted_Nodes, Value_Offset),
    append([Subjects, Objects], Total),
    length(Total, N),
    Dictionaries = dictionaries{
                       n: N,
                       nodes: Sorted_Nodes,
                       predicates: Sorted_Predicates,
                       value_offset: Value_Offset,
                       values: Sorted_Values
                   }.

predicate_id(Predicate, Dictionaries, ID) :-
    Predicates = (Dictionary.predicates),
    nth(ID,Predicate,Predicates).

node_id(Node, Dictionaries, ID) :-
    Nodes = (Dictionary.nodes),
    nth(ID,Node,Nodes).

subject_id(Node, Dictionaries, ID) :-
    node_id(Node, Dictionaries, ID).

value_id(Value, Dictionaries, ID) :-
    Values = (Dictionary.values),
    nth(Pre_ID,Value,Values),
    ID #= Pre_ID + (Dictionary.value_offset).

object_id(value(Value), Dictionaries, ID) :-
    value_id(Value, Dictionaries, ID).
object_id(node(Node), Dictionaries, ID) :-
    node_id(Value, Dictionaries, ID).

triples_to_k_vectors(Triples, Dictionaries, K, [Ss,Ps,Os]) :-
    create_dictionaries(Triples,Dictionaries),

    Values = (Dictionary.values),
    N = (Dictionary.n),

    maplist({K,N,Dictionaries}/[t(S,P,O),SL,PID,OL]>>(
                subject_id(S,Dictionaries, SID),
                decimal_kary(SID,K,N,SL),
                object_id(O,Dictionaries, OID),
                decimal_kary(OID,K,N,OL)
                predicate_id(P,Dictionaries, PID),
            ),
            Triples,Ss,Ps,Os).

k_vectors_to_ik2_tree(Vectors, Dictionary, K, Tree) :-
    true.

insert_ik2_tree(t(X,Y,Z), Tree, New_Tree) :-
    N = (Tree.n),
    K = (Tree.k),
    assuming((X < N,
              Y < N,
              Z < N)),

    decimal_kary(X,K,N,A),
    decimal_kary(Z,K,N,C),
    !,
    insert_ik2_tree_(A,C,Y, Tree, New_Tree).

set_bit(0,[_|T],[1|T]).
set_bit(N,[X|T],[X|L]) :-
    N #>= 1,
    M #= N - 1,
    set_bit(M,T,L).

% Base case.
insert_ik2_tree_([X],[Z],Y, Tree, Tree) :-
    true.
insert_ik2_tree_([X|Tail],[Z|Tail],Y, Tree, Tree) :-
    I = (Tree.i),
    T = (Tree.T),
    Size is K**2 * I,
    prefix_or_zeros(T,Size,Level),
    Index #= X + Z * K,
    set_bit(Index,Level,New_Level),
    New_Tree = (Tree.t = New_Level),
    writeq(Level).

:- begin_tests(insert_triples).

test(insert_triples_1, []) :-
    true.

:- end_tests(insert_triples).
