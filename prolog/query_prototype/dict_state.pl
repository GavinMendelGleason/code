:- module(dict_state,[
              update//3,
              view//2,
              put//2,
              peek//1,
              return//1,
              run/3
          ]).

/*******
 * Monadic DCG management
 *
 * We use DCG's to simplify tracking the state of the WOQL query compiler.
 */

/* Monadic selection */
update(Key,C0,C1,S0,S1) :-
    C0 = S0.Key,
    S1 = S0.put(Key, C1).

view(Key,C0,S0,S0) :-
    C0 = S0.Key.

swap(Key,C0,C1,S0,S1) :-
    C0 = S0.Key,
    C1 = S1.Key.

put(Key, C0, S0, S1) :-
    S1 = S0.put(Key, C0).

peek(S0,S0,S0).

return(S0,_,S0).

/* We should have a rule like phrase/2 and phrase/3 */
:- meta_predicate run(2,?,?).
run(DCG,Initial_State,Final_State) :-
    call(DCG,Initial_State,Final_State).

/*

Examples

*/

:- begin_tests(dict_state).

test(put, []) :-
    Name = "Kantorovich",
    run(put(name, Name),context{},O),
    O = context{name:Name}.

test(update, []) :-
    Name = "Kantorovich",
    Original = context{ name: "Danzig" },

    run(update(name, Old_Name, Name),
        Original,
        New),

    New = context{name:"Kantorovich"},

    run(put(name, Old_Name),
        New,
        Final),

    Final = context{name:"Danzig"}.

test(view, []) :-
    Original = context{ name: "Danzig" },
    run(view(name, Name),Original, Original),
    Name = "Danzig".

:- end_tests(dict_state).
