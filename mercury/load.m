:- module load.

:- interface.
:- import_module io.

:- import_module dcg.

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

:- pred space(string::in, string::out) is semidet.
space --> " " .
space --> "\n" .
space --> "\t" .
space --> "\r" .

:- pred whitespace(string::in, string::out) is semidet.
whitespace --> space, whitespace .
whitespace --> "" .

htmlchar --> 
:- pred anyBut(char::in, char::out, string::in, string::out) is semidet.
anyBut(C,C1,[C1|T],T) -->
   \+ C = C1.

uriString(Sin,Sout,[C|U]) :- anybut(">",C,Sin,Sinter), uriString(Sinter,Sout,U).

:- pred uri(string::in, string::out, string::out) is semidet.
uri(Sin,Sout,U) -->
  "<", uriString(U), ">".

:- pred triple(string::in, string::in, triple::out) is semidet.
makeTriple(S,"http://www.w3.org/2001/XMLSchema#integer",l_int(I)) :-
	parse_int(S,I).
makeTriple(S,"http://www.w3.org/2001/XMLSchema#dateTime",l_date(D)) :-
	parse_date(S,D).
makeTriple(S,"http://www.w3.org/2001/XMLSchema#string",l_string(L)) :-
	parse_string(S,L).

:- pred triple(string::in, string::out, triple::out) is semidet.
triple(Triple) -->
	uri(US), ">", spaces, "<", uri(UP), ">",
    ( "<", uri(UO), ">", { Triple=o(US,UP,UO) }
	; str(S),
	  ( "@", str(L), { Triple=lang(S,L) }
	  ; "^^", str(T) { makeTriple(S,T,Triple) })).

:- pred read_triple(io:di,io:uo,triple) is semidet.
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
