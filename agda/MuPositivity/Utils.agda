
module Utils where

open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Product
open import Data.Vec
open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Data.Bool hiding (_≟_ ; _≤_ ; _<_)

≡n : ∀ {n} → Vec Set (suc n) → Set
≡n (A ∷ []) = {x y : A} → x ≡ y
≡n (A ∷ (B ∷ w)) = {x y : A} → x ≡ y → (≡n (B ∷ w))

DecEq : ∀ X → Set
DecEq X = Decidable (_≡_ {A = X})

n≤m⇒1+n≤1+m : ∀ n m → n ≤′ m → suc n ≤′ suc m
n≤m⇒1+n≤1+m n .n ≤′-refl = ≤′-refl
n≤m⇒1+n≤1+m n₁ _ (≤′-step p) with n≤m⇒1+n≤1+m n₁ _ p
n≤m⇒1+n≤1+m n₁ _ (≤′-step p) | res = ≤′-step res

1+n≤1+m⇒n≤m : ∀ n m → suc n ≤′ suc m → n ≤′ m
1+n≤1+m⇒n≤m n .n ≤′-refl = ≤′-refl
1+n≤1+m⇒n≤m n zero (≤′-step ())
1+n≤1+m⇒n≤m n (suc m) (≤′-step p) = ≤′-step (1+n≤1+m⇒n≤m n m p)

n≤m∧m≤n⇒n≡m : ∀ n m → n ≤ m → m ≤ n → n ≡ m
n≤m∧m≤n⇒n≡m zero .0 n≤m z≤n = refl
n≤m∧m≤n⇒n≡m (suc n) zero () z≤n
n≤m∧m≤n⇒n≡m (suc n) (suc m) (s≤s n≤m) (s≤s m≤n) = cong suc (n≤m∧m≤n⇒n≡m n m n≤m m≤n)

¬n<m⇒m≤n : ∀ n m → ¬ (n < m) → m ≤ n
¬n<m⇒m≤n zero zero ¬n<m = z≤n
¬n<m⇒m≤n zero (suc m) ¬n<m with ¬n<m (s≤s z≤n)
¬n<m⇒m≤n zero (suc m) ¬n<m | ()
¬n<m⇒m≤n (suc n) zero ¬n<m = z≤n
¬n<m⇒m≤n (suc n) (suc m) ¬n<m = s≤s (¬n<m⇒m≤n n m (λ x → ¬n<m (s≤s x)))

sn≡sm⇒n≡m : ∀ {n m} → suc n ≡ suc m → n ≡ m
sn≡sm⇒n≡m refl = refl

infix 6 _⇒_
_⇒_ : Bool → Bool → Bool
P ⇒ Q = not P ∨ Q

open import Level
record DecTotalOrderEq (C : Set) (_≼_ : Rel C Level.zero) : Set where
  field
    tri : Trichotomous _≡_ _≼_
    tran : Transitive _≼_
    _≼?_ : Decidable _≼_

  _≟_ : ∀ x y → Dec (x ≡ y)
  x ≟ y with tri x y
  x ≟ y | tri< a ¬b ¬c = no ¬b
  x ≟ y | tri≈ ¬a b ¬c = yes b
  x ≟ y | tri> ¬a ¬b c = no ¬b

