open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable
open import Level

module Subsumption
  (C : Set)
  (Atom : Set)
  (eqAtom : DecEq Atom)
  (eqC : DecEq C)
  (D : Set)
  (eqD : DecEq D)
  where


open import Monotonic C Atom eqAtom eqC D eqD
open ModalTransitionSystem renaming (⟦_⟧ to sem)

open import Membership

  
⟦_⟧ : Φ → Interpretation → Transitions → Subjects
⟦ φ ⟧ i 𝓣 = sem 𝓣 φ i 

_≼_ : Φ → Φ → Set 
φ ≼ ψ = ∀ 𝓣 i → ⟦ φ ⟧ i 𝓣 ⊆ ⟦ ψ ⟧ i 𝓣
  
open import Data.List
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)

oracle : Σ C (λ x → ⊤)
oracle = {!!}

decSubsumption : ∀ ψ φ → Dec (φ ≼ ψ)
decSubsumption (v x) (v x₁) with eqAtom x x₁
decSubsumption (v x) (v .x) | yes refl = yes (λ 𝓣 i p₁ p₂ → p₂)
decSubsumption (v x) (v x₁) | no ¬p = no (λ proof → let impossible = proof [] (badI x x₁) in {!!})
  where badI : Atom → Atom → Atom → Subjects
        badI x x₁ y with eqAtom x y
        badI x x₁ y | yes p = {!!}
        badI x x₁ y | no p = {!!}
decSubsumption (v x) (P x₁) = {!!}
decSubsumption (v x) (α[ a ] ψ) = {!!}
decSubsumption (v x) (ψ ⊗ ψ₁) = {!!}
decSubsumption (v x) (- ψ) = {!!}
decSubsumption (P x) ψ = {!!}
decSubsumption (α[ a ] φ) ψ = {!!}
decSubsumption (Φ ⊗ φ₁) ψ = {!!}
decSubsumption (- φ) ψ = {!!}
