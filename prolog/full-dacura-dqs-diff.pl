diff --cc applications/abox.pl
index f281e42,eaf0bee..0000000
--- a/applications/abox.pl
+++ b/applications/abox.pl
@@@ -407,10 -407,10 +407,10 @@@ notFunctionalPropertyIC(X,P,_,Instance,
      N \= 1,
      interpolate(['Functional Property ',P,' is not functional.'],Message),
      Reason = ['rdf:type'='NotFunctionalPropertyViolation',
--	      bestPractice=literal(type('xsd:boolean',false)),
--	      subject=X,
--	      predicate=P,
--	      message=Message].
++			  bestPractice=literal(type('xsd:boolean',false)),
++			  subject=X,
++			  predicate=P,
++			  message=Message].
  
  notInverseFunctionalPropertyIC(X,P,Y,Instance,Schema,Reason) :-
      inverseFunctionalProperty(P,Schema),
@@@ -419,23 -419,22 +419,23 @@@
      N \= 1,
      interpolate(['Functional Property ',P,' is not functional.'],Message),
      Reason = ['rdf:type'='NotInverseFunctionalPropertyViolation',
--	      bestPractice=literal(type('xsd:boolean',false)),
--	      subject=X,
--	      predicate=P,
--	      object=Y,
--	      message=Message].
++			  bestPractice=literal(type('xsd:boolean',false)),
++			  subject=X,
++			  predicate=P,
++			  object=Y,
++			  message=Message].
  
 +    
  localOrphanPropertyIC(X,P,Y,Instance,Schema,Reason) :-
 -    xrdf(X,P,Y,Instance), \+ P='http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
 -    orphanProperty(P,_,Schema,_), 
 -    interpolate(['No property class associated with property: ',P,'.'],Message),
 -    Reason=['rdf:type'='OrphanPropertyViolation',
 -	    bestPractice=literal(type('xsd:boolean',false)),
 -	    subject=X,
 -	    predicate=P,
 -	    object=Y,
 -	    message=Message].
 +	xrdf(X,P,Y,Instance), \+ P='http://www.w3.org/1999/02/22-rdf-syntax-ns#type',
-     orphanProperty(P,_,Schema,_), 
-     interpolate(['No property class associated with property: ',P,'.'],Message),
-     Reason=['rdf:type'='OrphanPropertyViolation',
- 	    bestPractice=literal(type('xsd:boolean',false)),
- 	    subject=X,
- 	    predicate=P,
- 	    object=Y,
- 	    message=Message].
++	orphanProperty(P,_,Schema,_), 
++	interpolate(['No property class associated with property: ',P,'.'],Message),
++	Reason=['rdf:type'='OrphanPropertyViolation',
++			bestPractice=literal(type('xsd:boolean',false)),
++			subject=X,
++			predicate=P,
++			object=Y,
++			message=Message].
   
  instanceSubjectBlankNode(X,Instance,_) :- xrdf(X,_,_,Instance), rdf_is_bnode(X).
  instancePredicateBlankNode(Y,Instance,_) :- xrdf(_,Y,_,Instance), rdf_is_bnode(Y).
diff --git a/applications/dacura.pl b/applications/dacura.pl
index 7f6b5d7..b79e45b 100644
--- a/applications/dacura.pl
+++ b/applications/dacura.pl
@@ -22,7 +22,7 @@
 :- use_module(test).
 :- use_module(query). 
 :- use_module(tbox).
-:- use_module(logic).
+%%%% :- use_module(logic).
 
 % Logging / Turn off for production
 :- use_module(library(http/http_log)).
diff --git a/applications/query.pl b/applications/query.pl
index a50c68d..82a3463 100644
--- a/applications/query.pl
+++ b/applications/query.pl
@@ -1,4 +1,3 @@
-
 :- module(query, [%% Give a class frame for a given class.
 			  classFrame/3,
 			  % Various class/entity queries 
@@ -29,7 +28,7 @@ Structure of template description
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
-Frame spec: 
+Frame grammar
 
 KeyValPairs := a = b
 Params := list keyValPairs
@@ -41,7 +40,55 @@ Op := and | or | xor
 Error := [type=Reason] + Params
 Reason := distortedFrame | ...
 
+We have a predicate frame(Frame). which is true if the frame matches the frame grammar, 
+and a predicate invalidFrame(Frame) which throws an exception of the frame grammar is 
+violated. 
+
 *******************************************************/
+	  
+propertyRestriction(true).
+propertyRestriction(L) :-
+	is_list(L),
+	member(type=Type, L),
+	member(Type,['and','or','not', 'xor']),
+	member(operands=Ops),
+	forall(propertyRestriction,Ops).
+propertyRestriction(L) :-
+	member(mincard=_,L),
+	member(valuesFrom=_,L).
+propertyRestriction(L) :-
+	member(maxcard=_,L),
+	member(valuesFrom=_,L).
+propertyRestriction(L) :-
+	member(card=_,L),
+	member(valuesFrom=_,L).
+propertyRestriction(L) :-
+	member(hasValue=_,L).
+propertyRestriction(L) :-
+	member(allValuesFrom=_,L).
+propertyRestriction(L) :-
+	member(someValuesFrom=_,L).
+
+prop(P) :-
+	member(type=Type,P),
+	member(Type, [objectProperty, datatypeProperty]),
+	member(domain=Domain,P),
+	member(range=Range,P),
+	(member(frame=Frame,P) -> frame(Frame)
+	 ; true),
+	(member(restriction=R,P) -> propertyRestriction(R)
+	 ; true).
+
+propertyFrame(Ps) :- forall(prop,Ps).
+
+logicalFrame(F) :-
+	member(type=Type, F),
+	member(Type,['and','or','not', 'xor']),
+	forall(operands=Ops),
+	forall(frame, Ops).
+
+frame(F) :- logicalFrame(F).
+frame(F) :- propertyFrame(F).
 
 % Type at which to "clip" graphs to form trees
 entity(Class,Schema) :-
@@ -50,18 +97,20 @@ entity(Class,Schema) :-
 allEntities(Schema,AE) :-
 	uniqueSolns(E,query:entity(E,Schema),AE).
 
-mostSpecificPropertiesHelper([],_,_,[]).
-mostSpecificPropertiesHelper([P|Rest],Properties,Schema,Out) :-
-	mostSpecificPropertiesHelper(Rest,Properties,Schema,Ok),
-	member(P2,Properties),
-	(strictSubsumptionPropertiesOf(P2,P,Schema) *-> Out = Ok
-	 ; Out = [P|Ok]).
+addMostSpecificProperty(Schema,P,PList,Rp) :-
+	% write('P: '),writeq(P),nl,
+	member(Q,PList), % write('Q: '),writeq(Q),nl,
+	(subsumptionPropertiesOf(P,Q,Schema) *-> select(Q,PList,PListp), Rp=[P|PListp], % write('P < Q'),nl
+	 ; (subsumptionPropertiesOf(Q,P,Schema) *-> Rp=PList, % write('Q < P'), nl
+		; Rp=[P|PList])), !.
+addMostSpecificProperty(Schema,P,PList,[P|PList]).
 
-mostSpecificProperties(Ps1,Schema,Ps2) :-
-	mostSpecificPropertiesHelper(Ps1,Ps1,Schema,Ps2).
+mostSpecificProperties(Schema,Properties,SpecificProperties) :-
+	foldl(addMostSpecificProperty(Schema),Properties,[],SpecificProperties). 
 
-classProperties(Class, Schema, Properties) :-
-	uniqueSolns(P,tbox:anyDomain(P,Class,Schema),Properties).
+classProperties(Class, Schema, PropertiesPrime) :-
+	uniqueSolns(P,tbox:anyDomain(P,Class,Schema),Properties),
+	mostSpecificProperties(Schema,Properties,PropertiesPrime).
 
 :- rdf_meta hasFormula(r,o).
 hasFormula(Class,Schema) :-
@@ -175,7 +224,7 @@ propertyFrame(Schema,C,P,property(restriction(true),[type=objectProperty,propert
 propertyFrame(Schema,C,P,property(restriction(true),[type=objectProperty,property=P,
 													 domain=C,
 													 range=R,
-													 frame=[type=entity,class=R|RLabel]|Label]) :-
+													 frame=[type=entity,class=R|RLabel]|Label])) :-
     maybeLabel(P,Schema,Label),
     mostSpecificRange(P,R,Schema),
     class(R,Schema),
@@ -193,11 +242,30 @@ propertyFrame(_,C,P,error([type=distortedFrame, property=P,
 
 disjointUnionFrames(Frames,xor(Frames)).
 
-unionFrames(Frames,or(Frames).
+addProperty(Schema,P,Frame,Rp) :-
+	write('P: '),writeq(P),nl,
+	member(Q,Frame), write('Q: '),writeq(Q),nl,
+	member(property=Prop, P),
+	member(property=Prop, Q),
+	member(domain=D, P),write('D: '),writeq(D),nl,
+	member(domain=E, Q),write('E: '),writeq(D),nl,
+	(subsumptionOf(D,E,Schema) *-> Rp=Frame, write('D < E'),nl
+	 ; (subsumptionOf(E,D,Schema) *-> select(Q,Frame,Framep), Rp=[P|Framep], write('E < D'),nl
+		; Rp=[P|Frame],nl,writeq('D <> E'))), !.
+addProperty(Schema,P,Frame,[P|Frame]) :- write('P <prop> Q'), nl.
+	
+	
+unionPropertyFrame(Schema,FrameA,FrameB,FrameC) :-
+	foldl(addProperty(Schema),FrameA,FrameB,FrameC).
+
+unionFramesTest(Schema,Frames,Frame) :-
+    foldl(unionPropertyFrame(Schema),Frames,[],Frame). 
+
+unionFrames(Frames,or(Frames)).
 
 intersectRestriction(true,S,S) :- !.
 intersectRestriction(S,true,S) :- !.
-intersectRestriction(restriction(S),restriction(R),restriction(and([S,R])). 	
+intersectRestriction(restriction(S),restriction(R),restriction(and([S,R]))). 	
 
 %%% DDD fix intersection restrictions
 intersectionProperty(property(R,P),property(S,Q),property(T,P)) :-
@@ -226,12 +294,12 @@ renameProperty(R,PropertyOld,PropertyNew,[property=PropertyNew|Rp]) :-
 intersectionFrame(Schema,xor(Frames),A,xor(NewFrames)) :-
 	maplist(intersectionFrame(Schema,A),Frames,NewFrames), !.
 intersectionFrame(Schema,A,xor(Frames),xor(NewFrames)) :-
-	maplist(intersectionFrame(Schema,A),R,F), !.
+	maplist(intersectionFrame(Schema,A),Frames,NewFrames), !.
 intersectionFrame(Schema,or(R),A,or(F)) :-
 	maplist(intersectionFrame(Schema,A),R,F), !.
 intersectionFrame(Schema,A,or(R),or(F)) :-
 	maplist(intersectionFrame(Schema,A),R,F), !.
-intersectionFrame(Schema,A,oneof(L),oneof(L)) :- !.
+intersectionFrame(_Schema,_A,oneof(L),oneof(L)) :- !.
     % ???
     % probably need to make a list of restriction objects where elt =  or something?
 intersectionFrame(_,FrameA,[],FrameA) :- !.
@@ -263,7 +331,7 @@ intersectionFrames(Schema,[A|Frames],Frame) :-
 :- rdf_meta classFrame(+,t,t,t).
 traverseClassFormula(_,_,class('http://www.w3.org/2002/07/owl#Thing'),
 					 [type=thing,class='http://www.w3.org/2002/07/owl#Thing']) :- !.
-traverseClassFormula(Schema,Properties,class(C),Frame) :-
+traverseClassFormula(Schema,Properties,class(C),properties(Frame)) :-
     classProperties(C,Schema,Properties2),
     union(Properties,Properties2,Properties3),
     maplist(propertyFrame(Schema,C),Properties3,Frame), !.
@@ -272,7 +340,7 @@ traverseClassFormula(Schema,Properties,C<D,Frame) :-
     union(Properties,Properties2,Properties3),
 	maplist(propertyFrame(Schema,C),Properties3,Frame1),
     traverseClassFormula(Schema,Properties3,D,Frame2),
-	intersectionFrames(Schema,[Frame1,Frame2],Frame), !.
+	intersectionFrames(Schema,[properties(Frame1),Frame2],Frame), !.
 traverseClassFormula(Schema,Properties,C=xor(L),Frame) :-
     classProperties(C,Schema,Properties2),
     union(Properties,Properties2,Properties3),
@@ -304,7 +372,7 @@ traverseClassFormula(_,_,restriction(L),restriction(L)) :- !.
 traverseClassFormula(_,Properties,F,FailureFrame) :-
 	interpolate([F],Msg),
 	FailureFrame=[type=failure, message='mangled frame',
-				  formula=Msg, properties=Properties]), !.
+				  formula=Msg, properties=Properties], !.
     
 :- rdf_meta classFrame(r,o,t).
 classFrame(Class, Schema, Frame) :-
