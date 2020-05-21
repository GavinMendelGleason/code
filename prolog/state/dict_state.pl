:- module(dict_state,[
              update//3,
              view//2,
              put//2,
              peek//1,
              return//1,
              run/3,
              test//0
          ]).

/*******
 * Mondic DCG management
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

run(DCG,Initial_State,Final_State) :-
    call(DCG,Initial_State,Final_State).

/*

Examples

*/

name_steve -->
    put(name, steve).

name(Name) -->
    put(name, Name).

write_temp_name(Name) -->
    update(name, Old_Name, Name),
    write_name,
    put(name, Old_Name).

write_name -->
    view(name, Name),
    { write(Name),nl }.


test -->
    name_steve,
    write_name,
    name(helen),
    write_name,
    write_temp_name(george),
    write_name.


