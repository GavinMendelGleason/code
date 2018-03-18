:- module main.
:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module adts, parser, string, list, maybe.

:- pred read_triple(text_input_stream::in, io::di, io::uo) is det.
read_triple(Stream,!IO) :-
	io.read_line_as_string(Stream, Result, !IO),
	(if Result=ok(String)
	 then to_char_list(String,CL),
	      (if triple(_Triple,CL,[])
		   then %io.write_string("Success!\n", !IO),
		        %format_triple(Triple,ST),
		        %io.write_string(ST ++ "\n", !IO),
			    read_triple(Stream,!IO)
		   else io.write_string("'" ++ String ++ "' is not parseable!\n", !IO))
	 else io.write_string("End of stream!\n", !IO)).

main(!IO) :-
	File = "/home/francoisbabeuf/Documents/code/mercury/triples/test.n3",
	open_input(File,MaybeStream,!IO),
	(if MaybeStream=ok(Stream)
     then read_triple(Stream,!IO)
	 else io.write_string("Failed to read!\n", !IO)).
