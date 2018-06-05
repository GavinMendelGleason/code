open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_] ; inspect)
open import Data.List

module Example
  (Atom : Set)
  (eq : Decidable (_≡_ {A = Atom}))
  where

open import Data.Sum renaming (_⊎_ to _∨_)
open import Relation.Nullary
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

⟨_↔_⟩ₐ : Atom → Atom → Atom → Atom
⟨ x ↔ y ⟩ₐ z with eq x z
⟨ x ↔ y ⟩ₐ z | yes p = y
⟨ x ↔ y ⟩ₐ z | no ¬p with eq y z
⟨ x ↔ y ⟩ₐ z | no ¬p | yes p = x
⟨ x ↔ y ⟩ₐ z | no ¬p₁ | no ¬p = z

dist : ∀ x y a b c → ⟨ x ↔ y ⟩ₐ (⟨ a ↔ b ⟩ₐ c) ≡ ⟨ ⟨ x ↔ y ⟩ₐ a ↔  ⟨ x ↔ y ⟩ₐ b ⟩ₐ (⟨ x ↔ y ⟩ₐ  c)
dist x y z w with eq x y
dist x y z w | res = {!!}

{-
Goal: (c : Atom) →
      (⟨ Atom ↔ eq ⟩ₐ x y (⟨ Atom ↔ eq ⟩ₐ z w c | eq z c)
       | eq x (⟨ Atom ↔ eq ⟩ₐ z w c | eq z c))
      ≡
      (⟨ Atom ↔ eq ⟩ₐ (⟨ Atom ↔ eq ⟩ₐ x y z | eq x z)
       (⟨ Atom ↔ eq ⟩ₐ x y w | eq x w) (⟨ Atom ↔ eq ⟩ₐ x y c | eq x c)
       | eq (⟨ Atom ↔ eq ⟩ₐ x y z | eq x z)
         (⟨ Atom ↔ eq ⟩ₐ x y c | eq x c))
-}
