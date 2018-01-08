:- module load.
:- interface.

:- import_module io.
:- import_module list.
:- import module char.

%:- import_module dcg.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- type date --->
     %    M   D   Y   H   M   S   Z
     date(int,int,int,int,int,int,int).

:- type literal --->
     l_int(int)
   ; l_string(string)
   ; l_date(date).   

:- type lang --->
   lang(string,string).

:- type triple --->
   o(string,string,string)
   ; l(string,string,literal).

:- pred digit(int::out,list(char)::in,list(char)::out).
digit("0") --> "0".
digit("1") --> "1".
digit("2") --> "2".
digit("3") --> "3".
digit("4") --> "4".
digit("5") --> "5".
digit("6") --> "6".
digit("7") --> "7".
digit("8") --> "8".
digit("9") --> "9".

alphaUpper --> charRange('A','Z') .

alphaLower --> charRange('a','z') .

alpha --> alphaUpper .
alpha --> alphaLower .

:- pred space(list(char)::in, list(char)::out) is semidet.
space --> " " .
space --> "\n" .
space --> "\t" .
space --> "\r" .

:- pred whitespace(list(char)::in, list(char)::out) is semidet.
whitespace --> space, whitespace .
whitespace --> "" .

:- pred htmlchar(list(char)::in, list(char)::out) is semidet.
htmlchar --> alpha.
htmlchar --> digit(_).
htmlchar --> anyOf("/:?&#=").

:- pred anyOf(list(char)::in, list(char)::in, list(char)::out) is semidet.
anyOf(S, [H|T], T) :-
	atom_codes(S,C), member(H,C) .

uriString(Sin,Sout,[C|U]) :- anybut(">",C,Sin,Sinter), uriString(Sinter,Sout,U).

:- pred uri(list(char)::out,list(char)::in, list(char)::out) is semidet.
uri(U) -->
  "<", uriString(U), ">".

:- pred makeTriple(list(char)::in, list(char)::in, triple::out) is semidet.
makeTriple(S,"http://www.w3.org/2001/XMLSchema#integer",l_int(I)) :-
	parse_int(S,I).
makeTriple(S,"http://www.w3.org/2001/XMLSchema#dateTime",l_date(D)) :-
	parse_date(S,D).
makeTriple(S,"http://www.w3.org/2001/XMLSchema#string",l_string(L)) :-
	parse_string(S,L).

:- pred triple(list(char)::in, list(char)::out, triple::out) is semidet.
triple(Triple) -->
	uri(US), ">", spaces, "<", uri(UP), ">",
    ( "<", uri(UO), ">", { Triple=o(US,UP,UO) }
	; str(S),
	  ( "@", str(L), { Triple=lang(S,L) }
	  ; "^^", str(T) { makeTriple(S,T,Triple) })).

:- pred read_triple(io:di,io:uo,triple::out) is semidet.
read_triple(!IO,Triple) :-
	io.read_line_as_string(Result, !IO),
	(if Result=ok(String),
      triple(String,"",Triple)
     then
	  io.write_string("Success!\n", !IO)
     else
	  io.write.string("Failure!\n", !IO)
	).

main(!IO) :-
	File = "/home/francoisbabeuf/tmp/instance.nt",
	io.read_file(File, !IO),
    read_triple(!IO,Triple),	   
    io.write_string("File read!\n", !IO).
