:- [library(hdt)].

prefix_expand(Prefixes,X,Y) :-
    (   X = P:XX
    ->  (   once(member(P:PP, Prefixes)),
            atom_concat(PP, XX, Y))
    ;   Y = X).

rdf(H, S, P, O) :-
    (   S = _-_
    ->  SS = S
    ;   S = Sp:St-Sm
    ->  SS = (Sp:St)-Sm
    ;   SS = S-_),

    (   P = _-_
    ->  PP = P
    ;   P = Pp:Pt-Pm
    ->  PP = (Pp:Pt)-Pm
    ;   PP = P-_),

    (   O = _-_
    ->  OO = O
    ;   O = Op:Ot-Om
    ->  OO = (Op:Ot)-Om
    ;   OO = O-_),

    rdf_1(H, SS, PP, OO).



rdf_1(Handle, Subject-SM, Predicate-PM, Object-OM) :-
    Handle = (hdt(H),prefixes(Prefixes)),
    (   ground(Subject)
    ->  (   prefix_expand(Prefixes, Subject, Subject_1),
            hdt_subject_id(H, Subject_1, S_Id))
    ;   SM = (_,S_Id)),

    (   ground(Predicate)
    ->  (   prefix_expand(Prefixes, Predicate, Predicate_1),
            hdt_predicate_id(H, Predicate_1, P_Id))
    ;   PM=(_,P_Id)),

    (   ground(Object)
    ->  (   prefix_expand(Prefixes, Object, Object_1),
            hdt_object_id(H, Object_1, O_Id))
    ;   OM=(_,O_Id)),


    hdt_search_id(H, S_Id, P_Id, O_Id),

    hdt_property(H, shared(N_Shared)),
    (   S_Id =< N_Shared
    ->  SM = (shared, S_Id)
    ;   SM = (subject, S_Id)),

    PM = (predicate, P_Id),

    (   O_Id =< N_Shared
    ->  OM = (shared, O_Id)
    ;   OM = (object, O_Id)).

resolve(Handle, X) :-
    is_list(X),
    !,
    maplist({Handle}/[E]>>(resolve(Handle, E)), X).

resolve(Handle, T-M) :-
    Handle = (hdt(H),_),
    (   ground(T)
    ->  true
    ;   M = (shared, S_Id)
    ->  hdt_subject_id(H, T, S_Id)
    ;   M = (subject, S_Id)
    ->  hdt_subject_id(H, T, S_Id)
    ;   M = (predicate, P_Id)
    ->  hdt_predicate_id(H, T, P_Id)
    ;   M = (object, O_Id)
    ->  hdt_object_id(H, T, O_Id)).

example_ttl("
@prefix x: <http://datachemist.net/cow_food#> .
x:cow x:says \"moo\" .
x:cow x:eats x:grass .
x:grass x:color \"green\" .
x:sky x:color \"blue\" .
x:sky x:eats x:nothing .
").

prepare_example_hdt(Handle) :-
    example_ttl(Ttl),
    tmp_file_stream(File, Stream, [extension(ttl)]),
    format(Stream, "~a", [Ttl]),
    close(Stream),

    file_name_extension(Base, _, File),
    atom_concat(Base, '.hdt', Hdt_File),

    format(atom(Command), "rdf2hdt -f ttl ~a ~a", [File, Hdt_File]),
    shell(Command),

    hdt_open(Hdt, Hdt_File),
    Handle=(hdt(Hdt),prefixes([x:'http://datachemist.net/cow_food#'])).

example :-
    prepare_example_hdt(H),

    rdf(H, X, x:says, '"moo"'),
    rdf(H, X, x:eats, Y), % X never gets resolved, and the metadata is used without extra syntax
    rdf(H, Y, x:color-Color, Z), % but it is possible to grab the metadata for later use.
    rdf(H, x:sky, _-Color, S), % and now we use just the metadata, skipping the id retrieval for the color predicate

    resolve(H, [Z,S]),

    Z = Result-_,
    S = Sky_Color-_,

    resolve(H, S),

    format("color of the thing that the thing that says moo eats: ~a\n", Result),
    format("the color of the sky is: ~a\n", Sky_Color).

