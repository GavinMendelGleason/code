module Church where

open import Level renaming (zero to lzero; suc to lsuc)

Nat : ∀ α → Set (lsuc α)
Nat α = (A : Set α) → A → (A → A) → A

zero : ∀ α → Nat α
zero α = λ A z s → z

suc : ∀ α → Nat α → Nat α
suc α n = λ A z s → n A z s

add : ∀ α → Nat α → Nat α → Nat α
add α n m = λ A z s → n A (m A z s) s

_×_ : ∀ {α β} → Set α → Set β → Set ((lsuc α) ⊔ (lsuc β))
A × B = ∀ (C : Set _) → (A → B → C) → C
