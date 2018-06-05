--open import Utilities.Logic
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable

module MuPlus
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

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool hiding (_≟_)
open import Data.List
open import Induction.WellFounded
open import Data.Nat

import Database as DB
module DBmodule = DB Atom X D eqAtom eqX eqD DT ⊢ᵟ_∶_ typeDec
open DBmodule public

Interpretation : Set
Interpretation = Atom → Subjects

infixl 21 _⊕_
infixl 21 _⊗_
data Shape : Set where
  ⊥ : Shape
  ⊤ : Shape
  α⟨_⟩_ : (a : X) → Shape → Shape
  α[_]_ : (a : X) → Shape → Shape
  ℓ⟨_⟩_ : (a : X) → DT → Shape
  ℓ[_]_ : (a : X) → DT → Shape
  _⊕_ : Shape → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  _has_ : Shape → ℕ → Shape
  -- Loops
  μ : Atom → Shape → Shape
  v : Atom → Shape
  -- Negation
  -_ : Shape → Shape

open import FinSet
open FinSet.WF⊂mod

mutual
 
  fpWF : Atom → Shape → Interpretation → (S : Subjects) → Transitions → Terminals → (Acc _⊂_ S) → Subjects
  fpWF x φ i S 𝓣 𝓛 a with ⟦ φ ⟧ i S 𝓣 𝓛
  fpWF x φ i S 𝓣 𝓛 a | S' with S' ⊂? S
  fpWF x φ i S 𝓣 𝓛 (acc rs) | S' | yes p = fpWF x φ ((i [ x ≔ S ])) S' 𝓣 𝓛 (rs S' p)
  fpWF x φ i S 𝓣 𝓛 a | S' | no ¬p = S

  fp : Atom → Shape → Interpretation → Subjects → Transitions → Terminals → Subjects
  fp x φ i S 𝓣 𝓛 = fpWF x φ i S 𝓣 𝓛 (wf⊂ S)
  
  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  ⟦_⟧ : Shape → (i : Interpretation) → Subjects → Transitions → Terminals → Subjects
  ⟦ ⊥ ⟧ i S 𝓣 𝓛 = ∅
  ⟦ ⊤ ⟧ i S 𝓣 𝓛 = 𝓓 𝓣 ∪ 𝓓 𝓛
  ⟦ α⟨ a ⟩ φ ⟧ i S 𝓣 𝓛 = ⟪ s ∈ S ∣ ∃[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ∧ ⌊ t ∈? (⟦ φ ⟧ i S 𝓣) ⌋ ⟫
  ⟦ α[ a ] φ ⟧ i S 𝓣 𝓛 = ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i S 𝓣) ⌋ ⟫
  ⟦ ℓ⟨ a ⟩ τ ⟧ i S 𝓣 𝓛 = ⟪ s ∈ S ∣ ∃[ l ∈ 𝓡 𝓛 ] ⌊ (s , a , l) ∈term? 𝓣 ⌋ ∧ ⌊ typeDec l τ ⌋ ⟫
  ⟦ ℓ[ a ] τ ⟧ i S 𝓣 𝓛 = ⟪ s ∈ S ∣ Π[ l ∈ 𝓡 𝓛 ] ⌊ (s , a , l) ∈term? 𝓣 ⌋ ⇒ ⌊ typeDec l τ ⌋ ⟫
  ⟦ φ ⊕ φ₁ ⟧ i S 𝓣 𝓛 = (⟦ φ ⟧ i S 𝓣) ∪ (⟦ φ₁ ⟧ i S 𝓣) 
  ⟦ φ ⊗ φ₁ ⟧ i S 𝓣 𝓛 = (⟦ φ ⟧ i S 𝓣) ∩ (⟦ φ₁ ⟧ i S 𝓣)
  ⟦ φ has n ⟧ i S 𝓣 𝓛 with (length (⟦ φ ⟧ i S 𝓣 𝓛)) ≟ n
  ⟦ φ has n ⟧ i S 𝓣 𝓛 | yes p = ⟦ φ ⟧ i S 𝓣 𝓛
  ⟦ φ has n ⟧ i S 𝓣 𝓛 | no ¬p = ∅
  ⟦ μ x φ ⟧ i S 𝓣 𝓛 = fp x φ i S 𝓣 𝓛
  ⟦ v x ⟧ i S 𝓣 𝓛 = i x 
  ⟦ - φ ⟧ i S 𝓣 𝓛 = (𝓓 𝓣 ∪ 𝓓 𝓛) ̸ ⟦ φ ⟧ i S 𝓣 𝓛

  -- Some possible extensions:

  -- Parametric Shapes
  --  Π : Atom → Shape → Shape
  --  _·_ : Shape → Shape → Shape 

_·_⊢_∶_ : Transitions → Terminals → X → Shape → Set
𝓣 · 𝓛 ⊢ x ∶ φ = x ∈ ⟦ φ ⟧ (λ _ → 𝓓 𝓣 ∪ 𝓡ₛ 𝓣) (𝓓 𝓣 ∪ 𝓡ₛ 𝓣) 𝓣

checkφ : ∀ 𝓣 𝓛 x φ → Dec ( 𝓣 · 𝓛 ⊢ x ∶ φ )
checkφ 𝓣 𝓛 x φ = x ∈? ⟦ φ ⟧ (λ _ → (𝓓 𝓣 ∪ 𝓓 𝓛 ∪ 𝓡ₛ 𝓣)) (𝓓 𝓣 ∪ 𝓓 𝓛 ∪ 𝓡ₛ 𝓣) 𝓣
