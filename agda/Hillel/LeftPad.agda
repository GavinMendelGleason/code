
module LeftPad where

open import Data.Char
open import Data.List
open import Data.Nat

String : Set
String = List Char

times : ℕ → Char → String
times zero c = []
times (suc n) c = c ∷ (times n c)

leftPad : Char → ℕ → String → String
leftPad c n s with length s 
leftPad c n s | res = times (n ∸ length s) c ++ s 

max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = (suc n)
max (suc n) (suc m) = suc (max n m)

leftPadSize : ∀ c n s → length (leftPad c n s) ≡ max (length s) (length n)
leftPadSize c n s = ? 
