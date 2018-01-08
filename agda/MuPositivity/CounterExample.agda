
module CounterExample where

open import Data.Nat
open import Data.Product
open import Data.List
open import Membership
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

open import Monotonic ℕ ℕ _≟_ _≟_ ℕ _≟_

A = 0
B = 1
C = 2
D = 3
E = 4
F = 5
G = 6
H = 7

{- Counter Example -}
𝓣 : Transitions
𝓣 = (A , B , C) ∷ (A , B , D) ∷ (E , B , F) ∷ []
open ModalTransitionSystem 𝓣

S : Set
S = List ℕ

i : Interpretation
i = (λ _ → [])

φ⟨_⟩ : (a : ℕ) → Φ+
φ⟨ a ⟩ = α⟨ B ⟩⁅ 1 ⁆ (v a)

X₁ : Subjects
X₁ = C ∷ ∅

Y₁ : Subjects
Y₁ = C ∷ D ∷ ∅

X₁⊆Y₁ : X₁ ⊆ Y₁
X₁⊆Y₁ .2 here = here
X₁⊆Y₁ x (there x∈X₁) = there (there x∈X₁)

reflRepl : ∀ a → (a ≟ a) ≡ yes refl
reflRepl a with (a ≟ a)
reflRepl a | yes refl = refl
reflRepl a | no ¬p = refl ↯ ¬p

φNotMonotone : ∀ (a : ℕ) → 
 ----------------------------------------------------------
  ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X₁ ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y₁ ]))
φNotMonotone a sub with a ≟ a
φNotMonotone a sub | yes p with sub 0 here
φNotMonotone a sub | yes p | ()
φNotMonotone a sub | no ¬p = refl ↯ ¬p

X₂ : Subjects
X₂ = C ∷ ∅

Y₂ : Subjects
Y₂ = C ∷ F ∷ ∅

X₂⊆Y₂ : X₂ ⊆ Y₂
X₂⊆Y₂ .2 here = here
X₂⊆Y₂ x (there x∈X₂) = there (there x∈X₂)

φNotAntitone : ∀ (a : ℕ) →
 ----------------------------------------------------------
  ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y₂ ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X₂ ]))
φNotAntitone a sub with a ≟ a
φNotAntitone a sub | yes p with sub 4 (there (there here))
φNotAntitone a sub | yes p | there (there ())
φNotAntitone a sub | no ¬p = refl ↯ ¬p
