:- module(difflist, [
              is_dl/1,
              append_dl/3,
              member_dl/2,
              push_dl/3,
              push_new_dl/3
          ]).

is_dl(dl(L,T)) :-
    var(L),
    !,
    T == L.
is_dl(dl([_|T],R)) :-
    is_dl(T-R).

append_dl(dl(X,Y), dl(Y,YT), dl(X,YT)).

member_dl(_,dl(L,_)) :-
    var(L),
    !,
    fail.
member_dl(X,dl([X|_R],_LT)).
member_dl(X,dl([_Y|R],LT)) :-
    member_dl(X,dl(R,LT)).

push_dl(X,dl(H,[X|NT]),dl(H,NT)).

push_new_dl(X,dl(H,T),dl(H,NT)) :-
    var(H),
    !,
    T = [X|NT].
push_new_dl(X,dl([X|R],T),dl([X|R],T)) :-
    !.
push_new_dl(X,dl([Y|R],T),dl([Y|L],LT)) :-
    !,
    push_new_dl(X,dl(R,T),dl(L,LT)).

:- begin_tests(difflist).

test(append_dl_dl1_dl2, []) :-
    DL1 = dl([1,2|T1],T1),
    DL2 = dl([3,4|T2],T2),
    difflist:append_dl(DL1,DL2,DL3),
    DL3 = dl([1,2,3,4|T3],T3),
    var(T3).

test(append_dl_dl1_empty, []) :-
    DL1 = dl([1,2|T1],T1),
    DL2 = dl(T2,T2),
    difflist:append_dl(DL1,DL2,DL3),
    DL3 = dl([1,2|T3],T3),
    var(T3).

test(append_dl_empty_dl2, []) :-
    DL1 = dl(T1,T1),
    DL2 = dl([1,2|T2],T2),
    difflist:append_dl(DL1,DL2,DL3),
    DL3 = dl([1,2|T3],T3),
    var(T3).

    append_dl(T-T,S-S,T-S).

test(member_dl, []) :-
    DL = dl([1,2,3|T],T),
    member_dl(3,DL),
    !,
    \+ member_dl(4,DL),
    var(T).

test(member_dl_comprehension, []) :-
    DL = dl([1,2,3|T],T),
    findall(X, member_dl(X,DL), Xs),

    Xs = [1,2,3].

test(push_dl, []) :-
    DL1 = dl([1,2,3|T],T),
    push_dl(4,DL1,DL),
    DL = dl(H,T1),
    H == [1,2,3,4|T1].

test(push_new_dl, []) :-
    DL1 = dl([1,2,3|T],T),
    push_new_dl(4,DL1,DL),
    DL = dl(H,T1),
    H == [1,2,3,4|T1].

test(push_new_dl, []) :-
    DL1 = dl([1,2,3|T],T),
    push_new_dl(3,DL1,DL),
    DL = dl(H,T1),
    H == [1,2,3|T1].

:- end_tests(difflist).
