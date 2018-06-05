
module Hillel where

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

data _∈_ : ℤ → List  ℤ → Set where
  here : ∀ {i l} → i ∈ (i ∷ l)
  there : ∀ {i j l} →  i ∈ l → i ∈ (j ∷ l)

nextLemma : ∀ {x y l} → x ∈ (y ∷ l) → ¬ (x ≡ y) → x ∈ l
nextLemma here nxy = refl ↯ nxy
nextLemma (there p) nxy = p

elt : (i : ℤ) → (L : List ℤ) → Dec (i ∈ L)
elt x [] = no (λ ())  
elt x (x₁ ∷ l) with x ≟ x₁ 
elt x (.x ∷ l) | yes refl = yes here
elt x (x₁ ∷ l) | no ¬p with elt x l
elt x (x₁ ∷ l) | no ¬p | (yes p) = yes (there p)
elt x (x₁ ∷ l) | no ¬p₁ | (no ¬p) = no (¬p ∘ (λ z → nextLemma z ¬p₁))

data _<∶_ : List ℤ → List ℤ → Set where
  empty : [] <∶ []
  skip : ∀ {x m l} → m <∶ l → x ∈ m → m <∶ (x ∷ l)
  add : ∀ {x m l} → m <∶ l → ¬ (x ∈ m) → (x ∷ m) <∶ (x ∷ l)

unique : (l : List ℤ) → Σ[ m ∈ List ℤ ] m <∶ l
unique [] = [] , empty
unique (x ∷ l) with unique l
unique (x ∷ l) | m , p with elt x m 
unique (x ∷ l) | m , p₁ | (yes p) = m , skip p₁ p
unique (x ∷ l) | m , p | (no ¬p) = x ∷ m , add p ¬p

_⊆_ : ∀ (m l : List ℤ) → Set
m ⊆ l = ∀ x → x ∈ m → x ∈ l

m⊆l⇒x∷m⊆x∷l : ∀ {x m l} → m ⊆ l → (x ∷ m) ⊆ (x ∷ l)
m⊆l⇒x∷m⊆x∷l q x here = here
m⊆l⇒x∷m⊆x∷l q x (there r) = there (q x r)
        
m<∶l⇒m⊆l : ∀ {m l} → m <∶ l → m ⊆ l
m<∶l⇒m⊆l empty = λ x z → z
m<∶l⇒m⊆l (skip p x₁) = λ x z → there (m<∶l⇒m⊆l p x z)
m<∶l⇒m⊆l {m} {l} (add p x₁) with m<∶l⇒m⊆l p
m<∶l⇒m⊆l {m} {l} (add p x₁) | res = λ x → m⊆l⇒x∷m⊆x∷l res x 
m<∶l⇒l⊆m : ∀ {m l} → m <∶ l → l ⊆ m
m<∶l⇒l⊆m empty = λ x z → z
m<∶l⇒l⊆m (skip p x₁) with m<∶l⇒l⊆m p
m<∶l⇒l⊆m (skip p x₁) | res = alreadyThere x₁ res
  where alreadyThere : ∀ {x m l} → x ∈ m → l ⊆ m → (x ∷ l) ⊆ m
        alreadyThere x∈m l⊆m x here = x∈m
        alreadyThere x∈m l⊆m x (there x∈x∷l) = l⊆m x x∈x∷l
m<∶l⇒l⊆m (add p x₁) with m<∶l⇒l⊆m p
m<∶l⇒l⊆m (add p x₁) | res = λ x → m⊆l⇒x∷m⊆x∷l res x
