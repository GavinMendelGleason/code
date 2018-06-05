--open import Utilities.Logic
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable
open import Level

module Monotonic
  (Atom : Set)
  (C : Set)
  (Atom : Set)
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
open import Data.Nat renaming (_≟_ to _≟ℕ_)
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


infixl 21 _⊗_
data Φ : Set where
  v : Atom → Φ
  P : Predicate → Φ
  α[_]_ : (a : C) → Φ → Φ
  α⟨_⟩_ : (a : C) → Φ → Φ
  _⊗_ : Φ → Φ → Φ
--  _has_ : Φ → ℕ → Φ
  -_ : Φ → Φ


data Φ+ : Set where
  v : Atom → Φ+
  P : Predicate → Φ+
  α[_]_ : (a : C) → Φ+ → Φ+
  α⟨_⟩_ : (a : C) → Φ+ → Φ+
  _⊗_ : Φ+ → Φ+ → Φ+
  β⟨_⟩[_]_ : (a : C) → ℕ → Φ+ → Φ+
  -_ : Φ+ → Φ+


module Positivity where
  module WFAtom = FinSet.WF⊂mod Atom eqAtom
  open WFAtom public
  open import Four

  _∈atom?_ : (x : Atom) → (L : List Atom) → Dec (x ∈ L)
  x ∈atom? S = eq2in eqAtom x S

  _⊸_ : List Atom → Atom → List Atom
  _⊸_ X x = ⟪ y ∈ X ∣ not ⌊ (eqAtom x y) ⌋ ⟫ 

  data Polarity : Φ → List Atom → List Atom → Set where
    Var : ∀ {x} → Polarity (v x) [ x ] []
    Prop : ∀ {p} → Polarity (P p) [] []
    Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p

  PositiveIn : Atom → Φ → Set
  PositiveIn a s = ∀ {a p n} → a ∉ n → Polarity s p n

module WFX = FinSet.WF⊂mod C eqC
open WFX hiding (NotInUnionLeft ; NotInUnionRight)

module ModalTransitionSystem (𝓣 : Transitions) where


  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y


  𝓢 : Subjects
  𝓢 = 𝓓 𝓣 ∪ 𝓡 𝓣 
  
  𝓥 : Predicate → Subjects
  𝓥 f = ⟪ s ∈ 𝓢 ∣ f s ⟫

  mutual

    ⟦_⟧ : Φ → (i : Interpretation) → Subjects
    ⟦ P p ⟧ i = 𝓥 p
    ⟦ α[ a ] φ ⟧ i = ⟪ s ∈ 𝓢 ∣ Π[ t ∈ 𝓢 ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i) ⌋ ⟫
    ⟦ α⟨ a ⟩ φ ⟧ i = ⟪ s ∈ 𝓢 ∣ ∃[ t ∈ 𝓢 ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? (⟦ φ ⟧ i) ⌋ ⟫
    ⟦ φ ⊗ φ₁ ⟧ i = (⟦ φ ⟧ i) ∩ (⟦ φ₁ ⟧ i)
    ⟦ v x ⟧ i = i x 
    ⟦ - φ ⟧ i = 𝓢 ̸ ⟦ φ ⟧ i

    ⟦_⟧+ : Φ+ → (i : Interpretation) → Subjects
    ⟦ P p ⟧+ i = 𝓥 p
    ⟦ α[ a ] φ ⟧+ i = ⟪ s ∈ 𝓢 ∣ Π[ t ∈ 𝓢 ] (⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧+ i) ⌋) ⟫
    ⟦ α⟨ a ⟩ φ ⟧+ i = ⟪ s ∈ 𝓢 ∣ ∃[ t ∈ 𝓢 ] (⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? (⟦ φ ⟧+ i) ⌋) ⟫
    ⟦ φ ⊗ φ₁ ⟧+ i = (⟦ φ ⟧+ i) ∩ (⟦ φ₁ ⟧+ i)
    ⟦ v x ⟧+ i = i x
    ⟦ β⟨ a ⟩[ n ] φ  ⟧+ i = ⟪ s ∈ 𝓢 ∣ Π[ t ∈ 𝓢 ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ (⌊ t ∈? (⟦ φ ⟧+ i) ⌋ ∧ ⌊ ∣ ⟦ φ ⟧+ i ∣⟨ eqC ⟩ ≟ℕ n ⌋)⟫    
    ⟦ - φ ⟧+ i = 𝓢 ̸ ⟦ φ ⟧+ i

  open Positivity

  mutual

    Monotone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ) → a ∉ n → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
            ⟦ φ ⟧ (i [ a ≔ X ]) ⊆ ⟦ φ ⟧ (i [ a ≔ Y ]) 
    Monotone i X Y a (v x) nin pos sub with eqAtom a x
    Monotone i X Y a (v .a) nin pos sub | yes refl = sub 
    Monotone i X Y a (v x) nin pos sub | no ¬p = λ x₁ z → z
    Monotone i X Y a (P x) nin pos sub = λ x₁ z → z
    Monotone i X Y a (α[ a₁ ] s) nin (Alpha pos) sub =
      WFX.ComprehensionLaw {𝓢} {𝓣 = 𝓣} (Monotone i X Y a s nin pos sub)
    Monotone i X Y a (s ⊗ s₁) nin (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      WFX.IntersectionLaw (Monotone i X Y a s (NotInUnionLeft n₂ nin) pos sub)
                          (Monotone i X Y a s₁ (NotInUnionRight n₁ nin) pos₁ sub)
    Monotone i X Y a (- s) nin (Not pos) sub =
      WFX.NegationLaw 𝓢 (Antitone i X Y a s nin pos sub)
  
    Antitone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ) → a ∉ p → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
      ⟦ φ ⟧ (i [ a ≔ Y ]) ⊆ ⟦ φ ⟧ (i [ a ≔ X ]) 
    Antitone i X Y a (v x) nip Var sub with eqAtom a x
    Antitone i X Y x (v .x) nip Var sub | yes refl = ⊥-elim $ nip here
    Antitone i X Y a (v x) nip Var sub | no ¬p = λ x₁ z → z 
    Antitone i X Y a (P x) nip pos sub = λ x₁ z → z
    Antitone i X Y a (α[ a₁ ] s) nip (Alpha pos) sub =
      WFX.ComprehensionLaw {𝓢} {𝓣 = 𝓣} (Antitone i X Y a s nip pos sub)
    Antitone i X Y a (s ⊗ s₁) nip (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      WFX.IntersectionLaw (Antitone i X Y a s (NotInUnionLeft p₂ nip) pos sub)
                          (Antitone i X Y a s₁ (NotInUnionRight p₁ nip) pos₁ sub) 
    Antitone i X Y a (- s) nip (Not pos) sub =
      WFX.NegationLaw 𝓢 (Monotone i X Y a s nip pos sub)
    

