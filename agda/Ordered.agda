open import Data.List
open import Data.Product
open import Data.Nat
open import Agda.Primitive
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (inspect)
open import Data.Bool
open import Function

ordered' : ℕ → List ℕ → Set
ordered' n [] = ⊤
ordered' n (x ∷ l) = (n ≤ x) × ordered' x l

ordered : List ℕ → Set
ordered [] = ⊤
ordered (x ∷ l) = ordered' x l

ordered_list : Set
ordered_list = Σ (List ℕ) (λ l → ordered l)

example : ordered_list
example =  1 ∷ 2 ∷ 3 ∷ [] ,  (s≤s z≤n) , ((s≤s (s≤s z≤n)) , ⊤.tt)

strip : forall {p} {P : Set p} ->  Dec P → Bool
strip (yes p₁) = true
strip (no ¬p) = false


insert' : ℕ → List ℕ → List ℕ
insert' x [] = [ x ]
insert' x (x₁ ∷ l) =  if strip (x ≤? x₁) then x ∷ x₁ ∷ l
                     else x₁ ∷ insert' x l

revert : ∀ {n m} -> m ≰ n -> n ≤ m
revert {zero} p = z≤n
revert {suc n} {zero} p = ⊥-elim (p z≤n)
revert {suc n} {suc m} p = s≤s (revert (p ∘ s≤s))

ordered'-insert' : ∀ {x x'} xs → x' ≤ x -> ordered' x' xs → ordered' x' (insert' x xs)
ordered'-insert'      []       p  tt     = p , tt
ordered'-insert' {x} (x₁ ∷ xs) p (q , o) with x ≤? x₁
... | yes r = p , r , o
... | no  c = q , ordered'-insert' xs (revert c) o

ordered-insert' : ∀ {x} xs → ordered xs → ordered (insert' x xs)
ordered-insert'      []       tt = tt
ordered-insert' {x} (x₁ ∷ xs) o  with x ≤? x₁
... | yes r = r , o
... | no  c = ordered'-insert' xs (revert c) o

insert : ℕ → ordered_list → ordered_list
insert x (xs , o) = insert' x xs , ordered-insert' xs o
