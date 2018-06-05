open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary

module Sub
  (Atom : Set)
  (X : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqX : DecEq X)
  (eqD : DecEq D)
  (DT : Set)
  (⊢ᵟ_∶_ : D → DT → Set)
  (typeDec : Decidable (⊢ᵟ_∶_))
  where

open import Data.String renaming (_≟_ to eqString)
open import Data.List 
import Mu
module MuMod = Mu Atom X D eqAtom eqX eqD DT ⊢ᵟ_∶_ typeDec
open MuMod public
open import FinSet

_≲_ : ∀ (φ₁ φ₂ : Shape) → Set
φ₁ ≲ φ₂ = ∀ 𝓣 → let db = (𝓓 𝓣 ∪ 𝓡ₛ 𝓣) in
                 let interp = (λ _ → db)
                 in ⟦ φ₁ ⟧ interp db 𝓣 ⊆ ⟦ φ₂ ⟧ interp db 𝓣


S⊆S∪R : ∀ S R → S ⊆ (S ∪ R)
S⊆S∪R [] R x ()
S⊆S∪R (x₁ ∷ S) R .x₁ here = {! !}
S⊆S∪R (x ∷ S) R x₁ (there x∈S) = {!!} 

⟦φ⟧⊆𝓢 : ∀ φ 𝓣 → ⟦ φ ⟧ (λ _ → 𝓓 𝓣 ∪ 𝓡ₛ 𝓣) (𝓓 𝓣 ∪ 𝓡ₛ 𝓣) 𝓣 ⊆ (𝓓 𝓣 ∪ 𝓡ₛ 𝓣)
⟦φ⟧⊆𝓢 ⊥ 𝓣 = λ x → λ ()
⟦φ⟧⊆𝓢 ⊤ 𝓣 = λ x x₁ → {!!}
⟦φ⟧⊆𝓢 (α⟨ a ⟩ φ) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (α[ a ] φ) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (ℓ⟨ a ⟩ x) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (ℓ[ a ] x) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (φ ⊕ φ₁) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (φ ⊗ φ₁) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (ν x φ) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (v x) 𝓣 = {!!}
⟦φ⟧⊆𝓢 (- φ) 𝓣 = {!!}

⊥≲φ : ∀ φ → ⊥ ≲ φ 
⊥≲φ φ = λ 𝓣 x → λ ()

φ≲⊤ : ∀ φ → φ ≲ ⊤ 
φ≲⊤ φ 𝓣 x ⟦φ₁⟧ = {!!}

_≲?_ : ∀ φ₁ φ₂ → Dec (φ₁ ≲ φ₂)
⊥ ≲? φ₂ = yes (⊥≲φ φ₂)
⊤ ≲? ⊥ = no (λ x → {!!})
⊤ ≲? ⊤ = yes (λ 𝓣 x z → z)
⊤ ≲? (α⟨ a ⟩ φ₂) = no {!!}
⊤ ≲? (α[ a ] φ₂) = no {!!}
⊤ ≲? (ℓ⟨ a ⟩ x) = no {!!}
⊤ ≲? (ℓ[ a ] x) = no {!!}
⊤ ≲? (φ₂ ⊕ φ₃) = {!!}
⊤ ≲? (φ₂ ⊗ φ₃) = {!!}
⊤ ≲? ν x φ₂ = {!!}
⊤ ≲? v x = {!!}
⊤ ≲? (- φ₂) = {!!}
(α⟨ a ⟩ φ) ≲? φ₂ = {!!}
(α[ a ] φ) ≲? φ₂ = {!!}
(ℓ⟨ a ⟩ x) ≲? φ₂ = {!!}
(ℓ[ a ] x) ≲? φ₂ = {!!}
(φ ⊕ φ₁) ≲? φ₂ = {!!}
(φ ⊗ φ₁) ≲? φ₂ = {!!}
ν x φ ≲? φ₂ = {!!}
v x ≲? φ₂ = {!!}
(- φ) ≲? φ₂ = {!!}
