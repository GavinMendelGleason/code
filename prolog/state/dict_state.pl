:- module(dict_state,[]).

/*******
 * Mondic DCG management
 *
 * We use DCG's to simplify tracking the state of the WOQL query compiler.
 */

get(Key,Value,Set) :-
    Value = Set.Key.

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

name_steve -->
    update(name, _Old_Name, New_Name),
    {
        New_Name = steve
    }.

name(Name) -->
    update(name, _Old_Name, Name).

write_name -->
    view(name, Name),
    {
        write(Name),
        nl
    }.


test -->
    name_steve,
    write_name,
    name(helen),
    write_name.


