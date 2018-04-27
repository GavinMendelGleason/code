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

:- pred newline(parserState::in, parserState::out) is nondet.
newline(State0,State1) :-
    s("\n",State0,State1),
    State1 = status(State0 ^ buffer,
                    (State0 ^  linenum) + 1,
                    (State0 ^ charnum) + 1).

:- pred space(parserState::in, parserState::out) is multi.
space --> s(" ").

:- pred whitespace(parserState::in, parserState::out) is multi.
whitespace(status(Buffer,CharNum,LineNum), State1) :- 
    string.between(Buffer, CharNum, CharNum + 1, S),
    (
        S = "\n",
        State1 = status(Buffer, CharNum + 1, LineNum + 1)
    ;   S = "\t",
        State1 = status(Buffer, CharNum + 1, LineNum)
    ;   S = "\r",
        State1 = status(Buffer, CharNum + 1, LineNum)
    ;   S = " ",
        State1 = status(Buffer, CharNum + 1, LineNum)
    ;   State1 = parseError("Could not consume whitespace", CharNum, LineNum)
    ).
whitespace(parseError(Msg,CharNum,LineNum),parseError(Msg,CharNum,LineNum)).

:- pred choose(pred(parserState, parserState),
               pred(parserState, parserState),
               parserState,
               parserState).
:- mode choose(pred(in, out) is multi, pred(in, out) is multi, in, out) is multi.
choose(P1,P2,S0,Sn) :-
    P1(S0,S1),
    (
        S1 = status(_Msg,_CharNum,_LineNum),
        Sn = S1
    ;   S1 = parseError(_Msg,_CharNum,_LineNum),
        P2(S0,Sn)
    ).

:- pred whitespaces(parserState::in, parserState::out) is multi.
whitespaces(!S) :-
    choose(
        whitespace,
        % <+>
        (pred(State0 :: in ,State2 :: out) is multi :-
             whitespace(State0,State1), whitespaces(State1,State2)),
        !S
    ).

:- pred aaas(parserState::in, parserState::out) is multi.
aaas --> s("aaa").

:- pred example(parserState::in, parserState::out) is multi.
example --> aaas, whitespaces, aaas.

:- pred newParserState(string::in, parserState::out) is det.
newParserState(String,status(String,0,0)).

main(!IO) :-
    S = "aaa\t\t\taaa",
    promise_equivalent_solutions [State1] (newParserState(S,State0),
                                           example(State0,State1)), 
    (
        State1 = parseError(Msg,CharNum,_LineNum),
        string.int_to_string(CharNum,CharNumString),
        io.write_string("Failed with "++Msg++" "++" at char "++CharNumString++"\n",!IO)
    ;
        State1 = status(Rest,_CharNum,_LineNum),
        io.write_string("consumed entire string "++Rest++"\n",!IO)
    ).
     
      
