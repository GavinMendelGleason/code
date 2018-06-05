
:- module test.

:- interface.
:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module int.


:- pred fib(int::in, int::out) is det.
fib(N, X) :-
 	(if N =< 2
	 then X = 1
	 else fib(N - 1, A), fib(N - 2, B), X = A + B
	).

main(IOState_in, IOState_out) :-
  io.write_string("Hello, World!\n", IOState_in, IOState_out).

%% (prolog-font-lock-keywords)

