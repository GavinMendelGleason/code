open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable

module MuMin
  (Atom : Set)
  (C : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqC : DecEq C)
  where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool hiding (_≟_)
open import Data.List
open import Induction.WellFounded
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import FinSet
open import Membership

import Database as DB
module DBmodule = DB Atom C eqAtom eqC
open DBmodule public

Interpretation : Set
Interpretation = Atom → Subjects

Predicate : Set
Predicate = C → Bool

module WFX = FinSet.WF⊂mod C eqC
open WFX hiding (NotInUnionLeft ; NotInUnionRight)

module WFA = FinSet.WF⊂mod C eqC
open WFA renaming (_∪_ to _∪_atom)

module ModalTransitionSystem (𝓣 : Transitions) where

  S : Subjects
  S = 𝓓 𝓣 ∪ 𝓡 𝓣 
   
  𝓥 : Predicate → Subjects
  𝓥 f = ⟪ s ∈ S ∣ f s ⟫

  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  Monotone : Atom → (Interpretation → Atom → Subjects → Subjects) → Set
  Monotone a f = ∀ {X Y} i → X ⊆ Y → (f i a X) ⊆ (f i a Y)


  mutual

    infixl 21 _⊗_
    data Φ : Set where
      v : Atom → Φ
      P : Predicate → Φ
      α[_]_ : (a : C) → Φ → Φ
      _⊗_ : Φ → Φ → Φ
      ν : ∀ a → ∀ (φ : Φ) → {pf : PositiveIn a φ} → Φ
      -_ : Φ → Φ

    data Polarity : Φ → List Atom → List Atom → Set where
      Var : ∀ {x} → Polarity (v x) [ x ] []
      Prop : ∀ {p} → Polarity (P p) [] []
      Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
      And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
      Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p


    PositiveIn : Atom → Φ → Set
    PositiveIn a s = ∀ {a p n} → a ∉ n → Polarity s p n
  


    fix : (a : Atom) → Interpretation → (f : Interpretation → Atom → Subjects → Subjects) → Monotone a f → Subjects
    fix a i f = {!!}

    ⟦_⟧ : Φ → (i : Interpretation) → Subjects
    ⟦ P p ⟧ i = 𝓥 p
    ⟦ α[ a ] φ ⟧ i = ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i) ⌋ ⟫
    ⟦ φ ⊗ φ₁ ⟧ i = (⟦ φ ⟧ i) ∩ (⟦ φ₁ ⟧ i)
    ⟦ v x ⟧ i = i x
    ⟦ ν a f M ⟧ i = fix a i f M
    ⟦ - φ ⟧ i = S ̸ ⟦ φ ⟧ i
