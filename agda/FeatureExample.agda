
module FeatureExample where

infix 30 _≡_ 
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

data List (A : Set) : Set where
  [] : List A
  ∷ : {x : A} → {xs : List A} → List A

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
_++_ {A} (∷ {x} {xs}) ys = ∷ {A} {x} {xs ++ ys}

++-comm : ∀ {A : Set} (xs ys zs : List A) → (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
++-comm [] ys zs = refl
++-comm ∷ [] zs = {!!}
++-comm ∷ ∷ [] = {!!}
++-comm (∷ {xs = []}) ∷ ∷ = {!!}
++-comm (∷ {xs = ∷}) ∷ ∷ = {!!}
