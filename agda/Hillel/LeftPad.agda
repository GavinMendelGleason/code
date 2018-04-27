
module LeftPad where

open import Data.Char
open import Data.List
open import Data.List.Properties
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Product

String : Set
String = List Char

times : ℕ → Char → String
times zero c = []
times (suc n) c = c ∷ (times n c)

leftPad : Char → ℕ → String → String
leftPad c n s = times (n ∸ length s) c ++ s 

max : ℕ → ℕ → ℕ
max zero m = m
max (suc n) zero = (suc n)
max (suc n) (suc m) = suc (max n m)

timeslen : ∀ n c → length (times n c) ≡ n
timeslen zero c = refl
timeslen (suc n) c with timeslen n c
timeslen (suc n) c | res = cong suc res

n∸0≡n : ∀ {n} → n ∸ 0 ≡ n
n∸0≡n = refl

n+0≡n : ∀ n → n + 0 ≡ n
n+0≡n zero = refl
n+0≡n (suc n) = cong suc (n+0≡n n)

n+suc≡sucn : ∀ n m → n + (suc m) ≡ suc (n + m)
n+suc≡sucn zero m = refl
n+suc≡sucn (suc n) m = cong suc (n+suc≡sucn n m) 

n∸l+l≡max·l·m : ∀ n l → n ∸ l + l ≡ max l n
n∸l+l≡max·l·m n zero = n+0≡n n
n∸l+l≡max·l·m zero (suc l) = refl
n∸l+l≡max·l·m (suc n) (suc l) rewrite n+suc≡sucn (n ∸ l) l
 = cong suc (n∸l+l≡max·l·m n l)

leftPadSize : ∀ c n s → length (leftPad c n s) ≡ max (length s) n
leftPadSize c n s rewrite length-++ (times (n ∸ length s) c) {ys = s} | timeslen (n ∸ length s) c
  | n∸l+l≡max·l·m n (length s) = refl

-- This is pointless and self evident
stringSuffix : ∀ c n s → Σ[ m ∈ String ] leftPad c n s ≡ m ++ s
stringSuffix c n s = times (n ∸ length s) c , refl
