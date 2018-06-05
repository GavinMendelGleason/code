
module Fulcrum where

open import Data.List
open import Data.Bool hiding (_≟_)
open import Data.Integer
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Empty
open import Function
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Data.Product
open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.List.Reverse
open import Data.List.Properties

{-
 The fulcrum of a sequence is the index that minimizes the differences of the sums of the left and right sides.
ex FindBestFulcrum([5, 5, 10]) == 1, as 5 + 5 = 10
FindFulcrum([1, 2, 3, 4, 5, -7]) == 2, as |1 + 2 + 3 - (4 + 5 - 7)| = 2
First we construct the running sums going both ways. Then we can calculate the value of a given fulcrum by subtracting the appropriate index from each other. See examples through code.
-}
import Data.Sign as Sign
import Data.Nat

runningSum : List ℤ → List ℤ
runningSum = foldr (λ x → λ {[] → x ∷ [] ; (y ∷ ys) → x + y ∷ (y ∷ ys)}) [] 

1+n≡1+m⇒n≡m : ∀ n m → 1 + n ≡ 1 + m → n ≡ m
1+n≡1+m⇒n≡m n m p = {!n!}

diffList : ∀ (l m : List ℤ) → length l ≡ length m → List ℤ
diffList [] [] p = []
diffList [] (x ∷ m) ()
diffList (x ∷ l) [] ()
diffList (x ∷ l) (y ∷ m) p = {!let !} -- x - y ∷ diffList l m {!!}

findFulcrum : List ℤ → ℤ 
findFulcrum xs =
  let backwards = runningSum xs in
  let forwards = runningSum (reverse xs)
  in {!zip!}
