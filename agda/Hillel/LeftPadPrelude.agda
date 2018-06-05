
module LeftPadPrelude where

{- Try a rewrite using Prelude -}

open import Prelude
open import Tactic.Nat

times : Nat → Char → List Char
times zero c = []
times (suc n) c = c ∷  (times n c)

leftPad : Char → Nat → List Char → List Char
leftPad c n s = times (n - length s) c ++ s 


timeslen : ∀ n c → length (times n c) ≡ n
timeslen zero c = refl
timeslen (suc n) c with timeslen n c
timeslen (suc n) c | res = cong suc res

length-++ : ∀ {A : Set} (xs : List A) {ys} → length (xs ++ ys) ≡ length xs + length ys
length-++ []       = refl
length-++ (x ∷ xs) = cong suc (length-++ xs)

leftPadSize : ∀ c n s → length (leftPad c n s) ≡ max (length s) n
leftPadSize c n s = by ?

{- 

rewrite length-++ (times (n ∸ length s) c) {ys = s} | timeslen (n ∸ length s) c
  | n∸l+l≡max·l·m n (length s) = refl
-}

-- This is pointless and self evident
--stringSuffix : ∀ c n s → Σ[ m ∈ String ] leftPad c n s ≡ m ++ s
--stringSuffix c n s = times (n ∸ length s) c , refl

