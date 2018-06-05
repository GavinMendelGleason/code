
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable
open import Level

module Subst
  (C : Set)
  (Atom : Set)
  (default : C)
  (_≼_ : Rel Atom zero)
  (tdoe : DecTotalOrderEq Atom _≼_)
  where

open import FinSet
open import Data.List
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Data.Unit hiding (_≟_)
open import Data.Empty

_≼?_ : ∀ x y → Dec (x ≼ y)
_≼?_ = DecTotalOrderEq._≼?_ tdoe

_≟_ : ∀ x y → Dec (x ≡ y)
_≟_ = DecTotalOrderEq._≟_ tdoe

{-
OrderedKeys : List (Atom × C) → Set
OrderedKeys [] = ⊤
OrderedKeys (x ∷ []) = ⊤
OrderedKeys ((a , c) ∷ (a₁ , c₁) ∷ X) with a ≼? a₁
OrderedKeys ((a , c) ∷ (a₁ , c₁) ∷ X) | yes p = OrderedKeys ((a₁ , c₁) ∷ X)
OrderedKeys ((a , c) ∷ (a₁ , c₁) ∷ X) | no ¬p = ⊥
-}

data OrderedKeys : List (Atom × C) → Set where
  base : OrderedKeys []
  one : ∀ {c} x → OrderedKeys ((x , c) ∷ [])
  next : ∀ {x c l d} y → y ≼ x → OrderedKeys ((x , c) ∷ l) → OrderedKeys ((y , d) ∷ (x , c) ∷ l)

Assoc : Set
Assoc = List (Atom × C)

_[_≔_] : Assoc → Atom → C → Assoc
[] [ x ≔ X ] = (x , X) ∷ []
((x , c) ∷ i) [ x₁ ≔ X ] with x₁ ≟ x
((x , c) ∷ i) [ x₁ ≔ X ] | yes p = (x₁ , X) ∷ i
((x , c) ∷ i) [ x₁ ≔ X ] | no ¬p with x₁ ≼? x
((x , c) ∷ i) [ x₁ ≔ X ] | no ¬p | yes p = (x₁ , X) ∷ (x , c) ∷ i
((x , c) ∷ i) [ x₁ ≔ X ] | no ¬p₁ | no ¬p = (x , c) ∷ (i [ x₁ ≔ X ]) 

_⟨_⟩ : Interp → Atom → C  
[] ⟨ x ⟩ = default
((x , X) ∷ i) ⟨ x₁ ⟩ with x ≟ x₁
((x , X) ∷ i) ⟨ x₁ ⟩ | yes p = X
((x , X) ∷ i) ⟨ x₁ ⟩ | no ¬p = i ⟨ x₁ ⟩ 


Overwrite : ∀ {x X Y i} → i [ x ≔ X ] [ x ≔ Y ] ≡ i [ x ≔ Y ]
Overwrite = {!!}

Swap : ∀ {x y X Y i} → x ≢ y → i [ x ≔ X ] [ y ≔ Y ] ≡ i [ y ≔ Y ] [ x ≔ X ]
Swap = {!!} 
