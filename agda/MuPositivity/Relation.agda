open import Utils

module Relation
  (C : Set)
  (eqC : DecEq C)
  (D : Set)
  (eqD : DecEq D)
  where

open import Data.List
open import Data.Bool
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function
open import FinSet
open import Membership

open import Database C C eqC eqC D eqD

module WFTrans = FinSet.WF⊂mod Transition eqTrans Terminal eqTerminal
open WFTrans renaming (_∈?_ to _∈?_)

module WFC = FinSet.WF⊂mod C eqC D eqD

-- Right restriction (at property a)
_⟨_⟩▹_ : ∀ (R : Transitions) (a : C) (A : List C)  → Transitions
R ⟨ a ⟩▹ A = ⟪ τ ∈ R ∣ ⌊ eqC (prop τ) a ⌋ ∧ ⌊ (obj τ) WFC.∈? A ⌋ ⟫

σ₁ : ∀ s R → Transitions
σ₁ s R = ⟪ τ ∈ R ∣ ⌊ eqC (sub τ) s ⌋ ⟫

𝓒 : ∀ s R → ℕ
𝓒 s R = length (σ₁ s R)

▹-monotonic : ∀ R a A B → A ⊆ B → (R ⟨ a ⟩▹ A) ⊆ (R ⟨ a ⟩▹ B)
▹-monotonic R a A B A⊆B =
   ImplicationLawRaw R (λ τ → ⌊ eqC (prop τ) a ⌋ ∧ ⌊ (obj τ) WFC.∈? A ⌋)
                       (λ τ → ⌊ eqC (prop τ) a ⌋ ∧ ⌊ (obj τ) WFC.∈? B ⌋)
                       (λ {s} →
                          let f = λ t → WFC.BoolSub {t = t} A⊆B
                              g = λ (τ : Transition) →
                                  ImplyAnd {⌊ eqC (prop τ) a ⌋}
                                           {⌊ (obj τ) WFC.∈? A ⌋}
                                           {⌊ (obj τ) WFC.∈? B ⌋}
                                           (f (obj τ))
                          in g s)

{-
▹-conservative : ∀ 𝓣 a s n A B → A ⊆ B → T ⌊ 𝓒 s (𝓣 ⟨ a ⟩▹ A) ≟ℕ n ⌋ → T ⌊ 𝓒 s (𝓣 ⟨ a ⟩▹ B) ≟ℕ n ⌋ 
▹-conservative 𝓣 a s n A B A⊆B = {!!}
-}
