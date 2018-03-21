:- module main.

:- interface.

:- import_module io, string, int.
   
:- type parserState --->
     parseError(
         msg :: string,
         errcharnum :: int,
         errlinenum :: int
     ) 
   ; status(
         buffer :: string,
         charnum :: int,
         linenum :: int
     ).

:- pred main(io::di, io::uo) is det.

:- implementation.

:- pred sub_string_count_aux(string :: in , string :: in , int :: in, int :: out) is semidet.
sub_string_count_aux(String,Sub,StartIdx,Count) :-
    if string.sub_string_search_start(String,Sub,StartIdx,Idx)
    then sub_string_count_aux(String,Sub,Idx,C), Count=C+1
    else Count = 0.

:- pred sub_string_count(string :: in , string :: in , int :: out) is semidet.
sub_string_count(String,Sub,Count) :-
    sub_string_count_aux(String,Sub,0,Count).

:- pred s(string::in, parserState::in, parserState::out) is multi.
s(TestString,status(Buffer,CharNum,LineNum),status(Buffer,CharNum+Len,LineNum)) :-
    string.length(TestString,Len),
    string.between(Buffer, CharNum, CharNum + Len, TestString).
s(TestString,status(Buffer,CharNum,LineNum),parseError(Msg,CharNum,LineNum)) :-
    Msg = "Unable to consume "++TestString++" in "++Buffer++"\n".
s(_TestString,parseError(Msg,Char,Linenum),parseError(Msg,Char,Linenum)).

:- pred aaas(parserState::in, parserState::out) is multi.
aaas --> s("aaa").

:- pred newline(parserState::in, parserState::out) is nondet.
newline(!State) :-
    s("\n",!State),
    !:State = !.State,
    !State ^ linenum := (!.State ^ linenum) + 1.

:- pred space(parserState::in, parserState::out) is multi.
space --> s(" ").

:- pred example(parserState::in, parserState::out) is multi.
example --> aaas, space, aaas.

:- pred newParserState(string::in, parserState::out) is det.
newParserState(String,status(String,0,0)).

main(!IO) :-
    S = "aaa bbb aaa",
    (if promise_equivalent_solutions [State1] (newParserState(S,State0),
                                               example(State0,State1))
     then (State1 = parseError(Msg,CharNum,_LineNum),
           string.int_to_string(CharNum,CharNumString),
           io.write_string("Failed with "++Msg++" "++" at char "++CharNumString++"\n",!IO)
         ; State1 = status(Rest,_CharNum,_LineNum),
           io.write_string("consumed entire string "++Rest++"\n",!IO)
         )
     else io.write_string("Example failed ",!IO)).
      
