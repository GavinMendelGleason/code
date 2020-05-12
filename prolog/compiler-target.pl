
/* 

h  i
 \/ 
  d  e   f  g
   \ /   \ /
    b     c
     \  / 
      a  

*/ 
xrdf(r1,p,a,g).
xrdf(r1,q,c,g).
xrdf(r2,p,a,g).
xrdf(r2,q,b,g).
xrdf(r3,p,b,g).
xrdf(r3,q,d,g).
xrdf(r4,p,b,g).
xrdf(r4,q,e,g).
xrdf(r5,p,c,g).
xrdf(r5,q,f,g).
xrdf(r6,p,c,g).
xrdf(r6,q,g,g).
xrdf(r7,p,d,g).
xrdf(r7,q,h,g).
xrdf(r8,p,d,g).
xrdf(r8,q,i,g).


is_new(triple(X,R,Y,G),TDB) :-
    (   var(TDB)
    ->  true
    ;   TDB = []
    ->  true
    ;   TDB=[triple(X,R,Y,G)|_Rest]
    ->  false
    ;   TDB=[_|Rest],
        is_new(triple(X,R,Y,G),Rest)).

ancestor(Used,Bound,OG,H-T,FH-FT,A,B) :-
    New_Used is Used + 1,
    (   New_Used > Bound        % We're in the fringe - our final lap
    ->  Head-Tail = FH-FT,
        H=T
    ;   Head-Tail = H-T
    ),
    
    (   xrdf(R1,p,A,g),
        xrdf(R1,q,B,g),
        is_new(triple(A,R1,B,g),OG), 
        Head=[triple(A,R1,B,g)|Tail]
        
    ;   xrdf(R2,p,A,g),
        xrdf(R2,q,IM,g),
        is_new(triple(A,R2,IM,g),OG), 
        Head=[triple(A,R2,IM,g)|T0],
        
        (   New_Used > Bound
        ->  false
        ;   ancestor(New_Used,Bound,OG,T0-Tail,FH-FT,IM,B)
        )
    ).

/* 

G = H,
ancestor(0,2,G,H-T,FH-FT,a,B).

*/ 
