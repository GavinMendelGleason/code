:- module(hdtTransactions, [], []).




graphQueue(G,Queue) :-
		Queue=1,
		%graph_hdt(HDT0,G), !,
		HDT = HDT0. 

%% xrdf(?X,?Y,?Z,+G) is nondet.
%%
%% The top level view on the state of the database is implemented by the xrdf predicate.
%% This predicate has a dynamic / journalled layer which provides online updates of the database
%% as a prolog assertion, and then does periodic stop-the-world re-generation of the hdts from
%% journal. 
xrdf(X,Y,Z,G) :-
		graph(G,HDT),
		false.