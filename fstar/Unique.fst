
module Unique

(*
open FStar.List
open FStar.Nat
open FSatr.Bool 
*) 

val subset : xs:(nat list) -> ys:(nat list) -> bool
let rec subset xs ys = function 
| [] -> True
| x :: xs -> member x ys && subset xs ys

// equivalent in the sense of a set (bi-subset inclusion) 
val equiv : xs:(nat list) -> ys:(nat list) -> bool
let equiv xs ys = subset xs ys && subset ys xs

val is_unique : xs:(nat list) -> bool 
let rec is_unique xs = function 
| [] -> true
| x :: xs -> not (member x xs) && is_unique xs

val unique : xs:(nat list) -> Tot (ys:(nat list){ is_unique xs && equiv xs ys })
let rec unique xs = function 
| [] -> [] 
| x :: xs -> 
  if member x xs 
  then unique xs 
  else x :: (unique xs)
