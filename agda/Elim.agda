
module Elim where

open import Relation.Nullary
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Data.Empty
open import Data.Sum renaming (_⊎_ to _∨_)

excludedMiddle⇒doubleNegation : ∀ (p : Set) → (p ∨ ¬ p) → (¬ ¬ p → p)
excludedMiddle⇒doubleNegation p (inj₁ x) q = x
excludedMiddle⇒doubleNegation p (inj₂ y) q =  y ↯ q

doubleNegation⇒excludedMiddle : ∀ (p : Set) → (¬ ¬ p → p) → (p ∨ ¬ p)
doubleNegation⇒excludedMiddle p f = {!!}
