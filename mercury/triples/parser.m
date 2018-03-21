:- module parser.

:- interface.
:- import_module char, list.
:- import_module adts.

:- pred triple(triple::out, list(char)::in, list(char)::out) is semidet.
:- pred format_triple(triple::in, string::out) is det.

:- implementation.

:- import_module bool, string, list, int, integer.

:- pred digit(char::out,list(char)::in,list(char)::out) is semidet.
digit('0') --> ['0'].
digit('1') --> ['1'].
digit('2') --> ['2'].
digit('3') --> ['3'].
digit('4') --> ['4'].
digit('5') --> ['5'].
digit('6') --> ['6'].
digit('7') --> ['7'].
digit('8') --> ['8'].
digit('9') --> ['9'].

:- pred charRange(char::in, char::in, list(char)::in, list(char)::out) is semidet.
charRange(C1,C2,[C0|S0],S0) :-
	to_int(C0,I0),
	to_int(C1,I1),
	to_int(C2,I2), 
	I0 =< I1, I0 >= I2.

:- pred alphaUpper(list(char)::in, list(char)::out) is semidet. 
alphaUpper --> charRange('A','Z') .

:- pred alphaLower(list(char)::in, list(char)::out) is semidet. 
alphaLower --> charRange('a','z') .

:- pred alpha(list(char)::in, list(char)::out) is semidet. 
alpha --> (alphaUpper -> {true} ; alphaLower) .

:- pred space(list(char)::in, list(char)::out) is semidet.
space --> ([' '] -> {true}
		  ; ['\n'] -> {true}
		  ; ['\t'] -> {true}
		  ; ['\r']).

:- pred spaces(list(char)::in, list(char)::out) is semidet.
spaces -->
	(space
	-> spaces
	 ; []).

:- pred htmlchar(list(char)::in, list(char)::out) is semidet.
htmlchar -->
	(alpha -> []
	; digit(_) -> []
	; anyOf(['/',':','?','&','#','='])).

:- pred anyOf(list(char)::in, list(char)::in, list(char)::out) is semidet.
anyOf(Cs, [H|T], T) :-
	member(H,Cs) .

:- pred notGreater(char::out, list(char)::in, list(char)::out) is semidet.
notGreater(X) --> [X], { X \= ('>') }.

:- pred uriString(list(char)::out, list(char)::in, list(char)::out) is semidet.
uriString(Chars) -->
	(if notGreater(X)
	 then uriString(Rest), { Chars = [ X | Rest] }
	 else {Chars = []}). 

% 2002-05-30T09:00:00
:- pred parse_dateTime(dateTime::out, list(char)::in, list(char)::out) is semidet.
parse_dateTime(Date) -->
	digit(Y1),digit(Y2),digit(Y3),digit(Y4),
	['-'],
	digit(Mo1),digit(Mo2),
	['-'],
	digit(D1),digit(D2),
	((['T'] ; [' ']),
	 digit(H1),digit(H2),[':'],digit(M1),digit(M2),[':'],digit(S1),digit(S2)
	),
	{
      from_char_list([Y1,Y2,Y3,Y4],YS),
	  to_int(YS,Y),

	  from_char_list([Mo1,Mo2],MoS),
	  to_int(MoS,Mo), 

	  from_char_list([D1,D2],DS),
	  to_int(DS,D), 

	  from_char_list([H1,H2],HS),
	  to_int(HS,H), 
	  
	  from_char_list([M1,M2],MS),
	  to_int(MS,M), 
	  
	  from_char_list([S1,S2],SS),
	  to_int(SS,S), 

	  Date = dateTime(Y,Mo,D,H,M,S,0)
	}.

:- pred dateTime_to_string(dateTime::in, string::out) is det.
dateTime_to_string(dateTime(Y,Mo,D,H,M,S,Z),DS) :-
	DS = int_to_string(Y) ++ "-" ++ 
	     int_to_string(Mo) ++ "-" ++ 
	     int_to_string(D) ++ "T" ++
		 int_to_string(H) ++ ":" ++
	     int_to_string(M) ++ ":" ++
	     int_to_string(S) ++ "Z" ++
         int_to_string(Z).
						  
:- pred uri(list(char)::out,list(char)::in, list(char)::out) is semidet.
uri(U) -->
  ['<'], uriString(U), ['>'].

:- pred makeLiteral(list(char)::in, list(char)::in, literal::out) is semidet.
makeLiteral(CS,T,L) :-
	if to_char_list("http://www.w3.org/2001/XMLSchema#integer",T)
	then to_char_list(S,CS),
	     integer.from_string(S,I),
         L = l_int(I)
	else if to_char_list("http://www.w3.org/2001/XMLSchema#dateTime",T)
	then parse_dateTime(D,CS,[]),
	     L = l_dateTime(D)
	else if to_char_list("http://www.w3.org/2001/XMLSchema#string",T)
	then to_char_list(S,CS),
		 L = l_string(S)
	else if to_char_list("http://www.w3.org/2001/XMLSchema#boolean",T)
	then to_char_list(S,CS),
         (if (S = "true" ; S = "1")
		  then L = l_boolean(yes)
          else if (S = "false" ; S = "0")
          then L = l_boolean(no)
          else fail)
    else fail.

:- pred notQuote(char::out, list(char)::in, list(char)::out) is semidet.
notQuote(X) --> [X], { X \= '"' }.

:- pred str(list(char)::out, list(char)::in, list(char)::out) is semidet. 
str(Chars) -->
	( notQuote(X)
	-> str(Xs), {Chars = [X | Xs]}
	; {Chars = []}).

%:- pred triple(triple::out, list(char)::in, list(char)::out) is semidet.
triple(Triple) -->
	uri(US), spaces, uri(UP), spaces, { to_char_list(Sub,US), to_char_list(Pred,UP) },
    (if [('<')], uriString(UO), { to_char_list(Obj,UO) }
	 then [('>')], { Triple=o(Sub,Pred,Obj) }
	 else ['"'],str(S),['"'],
	      (if ['@']
	       then str(L), { to_char_list(String,S),
						  to_char_list(Lang,L),
						  Triple=l(Sub,Pred,l_lang(String,Lang)) }
           else ['^','^'],
                [('<')], uriString(T), [('>')],
                { makeLiteral(S,T,Literal),
                  Triple=l(Sub,Pred,Literal)})),
    spaces,['.'], spaces.

%:- pred format_triple(triple::in, string::out) is semidet.
format_triple(o(S1,S2,S3),SO) :-
	SO = "<" ++ S1 ++ "> <" ++ S2 ++ "> <" ++ S3 ++ "> .\n".
format_triple(l(S1,S2,L),SO) :-
	StringPrefix = "<" ++ S1 ++ "> <" ++ S2 ++ ">",
	( L=l_int(I),
	  SO=StringPrefix ++ "\"" ++ to_string(I) ++ "\"" ++
		 "^^<http://www.w3.org/2001/XMLSchema#integer> .\n" 
	; L=l_string(S),
	  SO=StringPrefix ++ "\"" ++ S ++ "\"" ++ "^^<http://www.w3.org/2001/XMLSchema#string> .\n" 
	; L=l_dateTime(D),
	  dateTime_to_string(D,DS),
	  SO=StringPrefix ++ "\"" ++ DS ++ "\"" ++ "^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n"
    ; L=l_boolean(yes),
	  SO=StringPrefix ++ "\"true\"" ++ "^^<http://www.w3.org/2001/XMLSchema#bool> .\n"
    ; L=l_boolean(no),
	  SO=StringPrefix ++ "\"false\"" ++ "^^<http://www.w3.org/2001/XMLSchema#bool> .\n"
	; SO="Malformed (not possible)").
	  
