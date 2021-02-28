:- module(vam, [
    vam_prove/3
]).

% boiler plate

phrase_dl(Arg, L-T) :-
    phrase(Arg, L, T).

const(X) :-
    number(X).

% VAM code

clause(Head,Goals) -->
    head(Head),
    body(Goals).

body(true) -->
    [c-nogoal].
body(Goals) -->
    goallist(Goals),
    [c-lastcall],
    {Goals \= true}.

goallist(Goal) -->
    goal(Goal),
    {Goal \= (_,_)}.
goallist((GoalA,GoalB)) -->
    goallist(GoalA),
    [c-call],
    goallist(GoalB).

head(Head) -->
    [F/A],
    { functuniv(Head,F,A,L) },
    argumentlist(h,L).

goal(Goal) -->
    [c-goal,F/A],
    {functuniv(Goal,F,A,L)},
    argumentlist(g,L).

argument(X,Var) -->
    [X-fstvar,Var],
    {var(Var)}.
argument(X,Var) -->
    [X-nxtvar,Var],
    {var(Var)}.
argument(X,Const) -->
    [X-const,Const],
    {const(Const)}.
argument(X,Str) -->
    [X-struct,F/A],
    {\+ var(Str),
     functuniv(Str,F,A,L)},
    argumentlist(X,L).
argument(X,_)   -->
    [X-void].            % skip

argumentlist(_X,[]) -->
    [].
argumentlist(X,[E|Es]) -->
    argument(X,E),
    argumentlist(X,Es).

functuniv(Funct,F,A,L) :-
    functor(Funct,F,A),
    Funct =.. [F|L].


% unification/3: The unification instructions
%% unification(Head+Goal, HeadsIn-HeadsOut, GoalsIn-GoalsOut)
unification((h-const)+(g-const), [Const|Hs]-Hs, [Const|Gs]-Gs).
unification((h-struct)+(g-struct), [F/A|Hs]-Hs, [F/A|Gs]-Gs).
unification((h-void)+(g-void),Hs-Hs,Gs-Gs).                    % skip
unification((h-fstvar)+(g-void),[_HVarNr|Hs]-Hs,Gs-Gs).        % init h-fstvar
unification((h-fstvar)+(g-fstvar),[Var|Hs]-Hs,[Var|Gs]-Gs).    % init both
unification((h-fstvar)+(g-nxtvar),[Var|Hs]-Hs,[Var|Gs]-Gs).    % pass argument
unification((h-const)+(g-fstvar),[Const|Hs]-Hs,[Const|Gs]-Gs). % no trail check
unification((h-const)+(g-nxtvar),[Const|Hs]-Hs,[Const|Gs]-Gs). % trail check
unification((h-nxtvar)+(g-nxtvar),[Var|Hs]-Hs,[Var|Gs]-Gs).    % full unification
unification((h-void)+(g-struct),Hs-Hs,[F/A|Gs]-NGs) :-         % skip goal,
    phrase_dl(argument(g,_),[g-struct,F/A|Gs]-NGs).             % init some g-fstvar
unification((h-struct)+(g-fstvar),[F/A|Hs]-NHs,[GVarNr|Gs]-Gs) :-  % no trail check
    phrase_dl(argument(h,GVarNr),[h-struct,F/A|Hs]-NHs).

% resolution/5: Goal selection
%% resolution(Head+Goal, Heads, GoalsIn-GoalsOut, StackIn-StackOut, NextPred)
resolution((c-nogoal)+(c-call), [], [c-goal,F/A|Gs]-Gs, St-St, F/A).
resolution((c-goal)+(c-lastcall), [F/A|Hs], []-Hs, St-St, F/A).
resolution((c-goal)+(c-call), [F/A|Hs], Gs-Hs, St-[Gs|St], F/A).
resolution((c-nogoal)+(c-lastcall), [], []-Gs, [[c-goal,F/A|Gs]|St]-St, F/A).

% vam_prove/3: Abstract interpreter%% vam_prove(HeadList,GoalList,Stack)
vam_prove([c-nogoal],[c-lastcall],[]).
vam_prove([H|Hs],[G|Gs],St) :-
    unification(H+G,Hs-NHs,Gs-NGs),
    vam_prove(NHs,NGs,St).
vam_prove([H|Hs],[G|Gs],St) :-
    resolution(H+G,Hs,Gs-NGs,St-NSt,NextPred),
    vam_clause([NextPred|NHs]),
    vam_prove(NHs,NGs,NSt).

query(Query) :-
    phrase(body(Query),[c-goal,F/A|GoalCode]),
    % translation
    vam_clause([F/A|HeadCode]),
    vam_prove(HeadCode,GoalCode,[]).

% Program example. 
vam_clause(Clause) :-
    phrase(clause(p(x),(q,r)), Clause, []).
vam_clause(Clause) :-
    phrase(clause(p(y),true), Clause, []).
vam_clause(Clause) :-
    phrase(clause(q,true), Clause, []).
vam_clause(Clause) :-
    phrase(clause(r,true), Clause, []).
vam_clause(Clause) :-
    phrase(clause(eq(X,X),true), Clause, []).
