:- module(fold_solutions,
	      [sfoldr/3,
           sfoldl/3
	      ]).

val(1). 
val(2).
val(3).

:- meta_predicate sfoldl(3,1,+,-).
sfoldl(Fold,Solution,Zero,Result) :-
    (   call(Solution,X)
    ->  sfoldl(Fold,Solution,X,Next),
        call(Fold,X,Next,Result)
    ;   Result = Zero).

:- meta_predicate sfoldr(3,1,+,-).
sfoldr(Fold,Solution,Zero,Result) :-
    (   call(Solution,X)
    ->  call(Fold,X,Zero,Next),
        sfoldr(Fold,Solution,Next,Result),
    ;   Result = Zero).
