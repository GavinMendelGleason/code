open import Utils

module MonotonicProperties
  (C : Set)
  (eqC : DecEq C)
  (D : Set)
  (eqD : DecEq D)
  where

open import Data.List
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function
open import Data.Unit
open import Data.Sum
open import Membership
open import FinSet

module WFX = FinSet.WF⊂mod C eqC D eqD 
open WFX
open import Database C C eqC eqC D eqD 

open import Relation C eqC D eqD 

α⟨⟩-Monotonic : ∀ {S A B a} {𝓣 : Transitions} → A ⊆ B → 
   ⟪ s ∈ S ∣ ∃[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? A ⌋ ⟫ ⊆  
   ⟪ s ∈ S ∣ ∃[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? B ⌋ ⟫ 
α⟨⟩-Monotonic {S} {A} {B} {a} {𝓣} A⊆B =
  ImplicationLawRaw S (λ s → ∃[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? A ⌋)
                      (λ s → ∃[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? B ⌋)
                      (let f = λ t → BoolSub {t = t} A⊆B
                           g = λ s t → ImplyAnd
                                           {⌊ (s , a , t) ∈trans? 𝓣 ⌋}
                                           {⌊ t ∈? A ⌋}
                                           {⌊ t ∈? B ⌋}
                                           (f t)
                           h = λ s → ImpliesExists S
                                        (λ t → ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? A ⌋)
                                        (λ t → ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? B ⌋)
                                        (λ x → g s _ x)
                       in λ x → h _ x)

{-
α⟨⟩⁅⁆-Monotonic : ∀ {S A B a n} {𝓣 : Transitions} → A ⊆ B →
   ⟪ s ∈ S ∣ ⌊ 𝓒 s (𝓣 ⟨ a ⟩▹ A) ≟ℕ n ⌋ ⟫ ⊆ ⟪ s ∈ S ∣ ⌊ 𝓒 s (𝓣 ⟨ a ⟩▹ B) ≟ℕ n ⌋ ⟫
α⟨⟩⁅⁆-Monotonic {S} {A} {B} {a} {n} {𝓣} A⊆B = {!!}
  -}

α[]-Monotonic : ∀ {S A B a} {𝓣 : Transitions} → A ⊆ B →
 ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋ ⟫ ⊆
 ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋ ⟫
α[]-Monotonic {S} {A} {B} {a} {𝓣} A⊆B =
   ImplicationLawRaw S (λ s → Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋)
                       (λ s → Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋)
                       (let f = λ t → BoolSub {t = t} A⊆B
                            g = λ s t → ImpliesAbstract
                                           {⌊ (s , a , t) ∈trans? 𝓣 ⌋}
                                           {⌊ t ∈? A ⌋}
                                           {⌊ t ∈? B ⌋}
                                           (ImpBool (λ t → ⌊ t ∈? A ⌋)
                                                    (λ t → ⌊ t ∈? B ⌋)
                                                    t
                                                    (f t))
                            h = λ s → ImpliesAll S
                                        (λ t → ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? A ⌋)
                                        (λ t → ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? B ⌋)
                                        (g s _)
                        in λ x → h _ x)
