:- module(state,[]).

update(C0,C1,S0,S1) :-
    select(C0,S0,C1,S1).

view(C0,S0,S0) :-
    member(C0,S0).

return(S0,_,S0).

/* 
Now we can easily thread things together to have a "stateful" approach to manipulation. 

Imagine the following term language, a fragment of one cribbed from Dijkstra: 

<pre> 
Exp = V | 0..9 | Exp + Exp | Exp * Exp
C = C0;C1 | (V := Exp)  
</pre>

An interpreter for this language might be written in the following way: 

*/

eval(A + B, Val) -->
    eval(A,AVal),
    eval(B,BVal),
    {
        Val is AVal + BVal
    }.
eval(A * B, Val) -->
    eval(A,AVal),
    eval(B,BVal),
    {
        Val is AVal * BVal
    }.
eval(A, A) --> {number(A)}.
eval(A, V) -->
    {atom(A)},
    view(A=V).
    
interpret(C0;C1) --> 
    interpret(C0), 
    interpret(C1).
interpret(V:=Exp) -->
    eval(Exp,Val), 
    update(V=_,V=Val).


run :- 
    Term=(
        v := (1 + 3)
    ;   w := v + v
    ;   w := w + 1),
    interpret(Term,[v=0,w=0],Result), 
    write(Result).
 
/* 
Example = 
*/
