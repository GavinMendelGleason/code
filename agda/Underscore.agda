module Underscore where

open import Agda.Builtin.Equality
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

data A : Set where
  a1 a2 a3 : A

data P : A → Set where
  p-a1 : P a1
  p-a3 : P a3

data Q : A → Set where
  q-not-a2 : (x : A) → (x ≡ a2 → ⊥) → Q x

to : (x : A) → P x → Q x
to a1 p-a1 = q-not-a2 a1 (λ ())
to a2 ()
to a3 p-a3 = q-not-a2 a3 (λ ())

from : (x : A) → Q x → P x
from a1 (q-not-a2 .a1 x) = p-a1
from a2 (q-not-a2 .a2 x) = ⊥-elim (x refl)
from a3 (q-not-a2 .a3 x) = p-a3

from-to : (x : A) → (p : P x) → from x (to x p) ≡ p
from-to a1 p-a1 = refl
from-to a2 ()
from-to a3 p-a3 = refl

to-from : (x : A) → (q : Q x) → to x (from x q) ≡ q
to-from a1 (q-not-a2 .a1 x) = {!!}
to-from a2 (q-not-a2 .a2 x) = ⊥-elim (x refl)
to-from a3 (q-not-a2 .a3 x) = {!!}
