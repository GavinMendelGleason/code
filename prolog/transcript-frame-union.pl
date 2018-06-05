
Schema=testing,
Frames=[[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',
		  domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
		  range='http://www.w3.org/2001/XMLSchema#integer',
		  restriction=true,
		  label=literal(lang(en,'Population'))],
		 [type=datatypeProperty,
		  property='http://dacura.cs.tcd.ie/data/seshattiny#population',
		  domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		  range='http://www.w3.org/2001/XMLSchema#integer',
		  restriction=true,label=literal(lang(en,'Population'))],
		 [type=datatypeProperty,
		  property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',
		  domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		  range='http://www.w3.org/2001/XMLSchema#string',restriction=true,
		  label=literal(lang(en,'Alternative name'))],
		 [type=datatypeProperty,
		  property='http://dacura.cs.tcd.ie/data/seshattiny#name',
		  domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		  range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))],

		[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',
		  domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
		  range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',
		  domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
		  range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]]]],
unionFramesTest(Schema,Frames,Frame), writeq(Frame).

Schema=testing,
A=[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',
   domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
   range='http://www.w3.org/2001/XMLSchema#integer',
   restriction=true,
   label=literal(lang(en,'Population'))],
B=[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',
   domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
   range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
unionProperty(A,B,C,Schema).


Schema=testing,
FrameA=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
		 range='http://www.w3.org/2001/XMLSchema#integer',
		 restriction=true,
		 label=literal(lang(en,'Population'))],
		[type=datatypeProperty,
		 property='http://dacura.cs.tcd.ie/data/seshattiny#population',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		 range='http://www.w3.org/2001/XMLSchema#integer',
		 restriction=true,label=literal(lang(en,'Population'))],
		[type=datatypeProperty,
		 property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		 range='http://www.w3.org/2001/XMLSchema#string',restriction=true,
		 label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,
		 property='http://dacura.cs.tcd.ie/data/seshattiny#name',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		 range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
FrameB=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',
		  domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
		  range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',
		 domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
		 range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
unionPropertyFrame(Schema,FrameA,FrameB,FrameC), writeq(FrameC).


[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]].



%	A=[1,2,3,6,9] /\ B=[1,4,5,6,8] /\ A\/B => { x | x in A /\ y in B }
% {x in A, B := B + x}


Schema=testing,
P=[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',
   domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
   range='http://www.w3.org/2001/XMLSchema#integer',
   restriction=true,
   label=literal(lang(en,'Population'))],
Q=[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
Frame=[Q],
addProperty(Schema,Frame, P, R). 

Schema=testing,
D='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
E='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
subsumptionOf(D,E,Schema).

addProperty(testing,[],[property='a'],R).

D='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
P=[property='a',domain=D],
Frame=[P],
addProperty(testing,Frame,P,R).


Schema=testing,
FrameA=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
FrameB=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
unionPropertyFrame(Schema,FrameA,FrameB,FrameC), writeq(FrameC).


Schema=testing,
FrameA=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
FrameB=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
unionFramesTest(Schema,[FrameA,FrameB],Frame), writeq(Frame).



Schema=testing,
FrameA=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',
		 range='http://www.w3.org/2001/XMLSchema#integer',
		 restriction=true,
		 label=literal(lang(en,'Population'))],
		[type=datatypeProperty,
		 property='http://dacura.cs.tcd.ie/data/seshattiny#population',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		 range='http://www.w3.org/2001/XMLSchema#integer',
		 restriction=true,label=literal(lang(en,'Population'))],
		[type=datatypeProperty,
		 property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		 range='http://www.w3.org/2001/XMLSchema#string',restriction=true,
		 label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,
		 property='http://dacura.cs.tcd.ie/data/seshattiny#name',
		 domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',
		 range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
FrameB=[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',
		  domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
		  range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
		[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',
		 domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',
		 range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]],
unionFramesTest(Schema,[FrameA,FrameB],FrameC), writeq(FrameC).






addProperty(Schema,P,Frame,Rp) :-
	member(Q,Frame),
	member(property=Prop, P),
	member(property=Prop, Q),
	member(domain=D, P),
	member(domain=E, Q),
	(subsumptionOf(D,E,Schema) *-> Rp=Frame, 
	 ; (subsumptionOf(E,D,Schema) *-> select(Q,Frame,Framep), Rp=[P|Framep],
		; Rp=[P|Frame])), !.
addProperty(Schema,P,Frame,[P|Frame]) :- !.
	
	
unionPropertyFrame(Schema,FrameA,FrameB,FrameC) :-
	foldl(addProperty(Schema),FrameA,FrameB,FrameC).

unionFrames(Schema,Frames,Frame) :-
    foldl(unionPropertyFrame(Schema),Frames,[],Frame). 




\
\




%% Not yet done?

[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Polity',range='ht\
tp://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/data/seshattiny#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]].


[[type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#population',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#integer',restriction=true,label=literal(lang(en,'Population'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#alternativeName',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Alternative name'))],
 [type=datatypeProperty,property='http://dacura.cs.tcd.ie/data/seshattiny#name',domain='http://dacura.cs.tcd.ie/ontology/utv#Entity',range='http://www.w3.org/2001/XMLSchema#string',restriction=true,label=literal(lang(en,'Name'))]].
