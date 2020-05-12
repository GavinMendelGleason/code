:- module(queue, [queue/1,queue/2]).

%% queue(-Q) is det. 
% The empty queue
queue(q(z,H,H)).

%% queue(+Elt,-Q) is det. 
% The one element queue
queue(H,q(s(z),[H|T],T)).

%% queue_head(+X,+Q1,-Q2) is det.
% Returns a queue with one more elt
%% queue_head(+X,-Q1,+Q2) is det.
% Returns a queue with one fewer elt.
queue_head(X,q(N,F,B), q(s(N),[X|F],B)).


%% queue_head_list(+L,-Q1,+Q2) is det.
% Returns a list from the top of the queue
queue_head_list([],Q,Q).
queue_head_list([X|Xs],Queue,Queue0) :-
    queue_head(X,Queue1,Queue0),
    queue_head_list(Xs,Queue,Queue1).

queue_last(X,q(N,F,[X|B]),q(s(N),F,B)).

queue_last_list([], Queue, Queue).
queue_last_list([X|Xs], Queuel, Queue) :-
    queue_last(X, Queuel, Queue2),
    queue_last_list(Xs, Queue2, Queue).

list_queue(List, q(Count,Front,Back)) :-
    list_queue(List,Count,Front,Back).

list_queue([],z,B,B).
list_queue([X|Xs],s(N),[X|F],B) :-
    list_queue(Xs,N,F,B).

queue_length(q(Count,Front,Back),Length) :-
    queue_length(Count,Front,Back,0,Length).

queue_length(z, Back, Back, Length, Length).
queue_length(s(N), [_|Front], Back, L0, Length) :-
    L1 is L0+1,
    queue_length(N, Front, Back, L1, Length).
