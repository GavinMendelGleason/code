mapm(P,L1,S0,SN) :-
    mapm_(L1,S0,SN,P).

mapm_([],S,S,_P).
mapm_([H|T],S0,SN,P) :-
    call(P,H,S0,S1),
    mapm_(T,S1,SN,P).

mapm(P,L1,L2,S0,SN) :-
    mapm_(L1,L2,S0,SN,P).

mapm_([],[],S,S,_P).
mapm_([H|T],[HP|TP],S0,SN,P) :-
    call(P,H,HP,S0,S1),
    mapm_(T,TP,S1,SN,P).

mapm(P,L1,L2,L3,S0,SN) :-
    mapm_(L1,L2,L3,S0,SN,P).

mapm_([],[],[],S,S,_P).
mapm_([H|T],[HP|TP],[HM|TM],S0,SN,P) :-
    call(P,H,HP,HM,S0,S1),
    mapm_(T,TP,TM,S1,SN,P).


read_both(X,Y) -->
    [X, Y].

test -->
    mapm(read_both, ["asdf", "fdsa"], ["X", "Y"]).
