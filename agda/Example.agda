module Example where

open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality as PropEq
     using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Data.Bool
open import Relation.Nullary
--open import Relation.Unary 


data Decidable {ℓ} (P : Set ℓ) : Set ℓ where
  yes : ( p :   P) → Decidable P
  no  : (¬p : ¬ P) → Decidable P

record Sortable (A : Set) : Set₁ where 
  constructor ⟨_⟩
  field 
    _≤_ :  A → A → Set
    reflexive : ∀ x → x ≤ x
    antisymetric : ∀ x y → x ≤ y → y ≤ x → x ≡ y
    transitve : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
    decidable : ∀ x y → Decidable (x ≤ y)

data Nat : Set where 
  zero : Nat 
  succ : Nat → Nat 

data _≤ℕ_ : Nat → Nat → Set where
  leZero : ∀ x → zero ≤ℕ x
  leNext : ∀ x y → x ≤ℕ y → (succ x) ≤ℕ (succ y)

invsucc : ∀ {x y} → ((succ x) ≤ℕ (succ y)) → x ≤ℕ y
invsucc {x} {y} (leNext .x .y p) = p 

decproof : ∀ x y → Decidable (x ≤ℕ y)
decproof zero y = yes (leZero y)
decproof (succ x) zero = no (λ ())
decproof (succ x) (succ y) with decproof x y
decproof (succ x) (succ y) | no p = no (λ x₁ → p (invsucc x₁))
decproof (succ x) (succ y) | yes p = yes (leNext x y p) 

_≤?_ : Nat → Nat → Bool 
x ≤? y with decproof x y 
x ≤? y | yes p = true 
x ≤? y | no p = false 

data Is : {A : Set} → A → Set₁ where 
  is : ∀ {A} → (x : A) → Is x

--test : Sortable Nat
--test = ⟨ le ⟩


{-  


open PropEq.≡-Reasoning

data Nat : Set where 
  zero : Nat 
  succ : Nat → Nat 

_+_ : Nat → Nat → Nat
zero + y = y
succ x + y = succ (x + y)
-}


{-

data Permutation 

data List (A : Set) : Set where 
  [] : List A
  _∷_ : A → List A → List A 
 
data Dec : Set → Set₁ where 
  dec : ∀ {A : Set} (x y : A) → ((x ≡ y) ⊎ (x ≡ y) → ⊥) → Dec A



insertionSort :: {Dec A} → A → List A 
insertionSort 


data Nat : Set where 
  zero : Nat
  succ : Nat → Nat

one : Nat 
one = succ zero
two : Nat 
two = succ one
three : Nat 
three = succ two

_+_ : Nat → Nat → Nat
zero     + y = y
(succ x) + y = succ (x + y)  

(succ (succ (succ zero))) + (succ zero) 

x = (succ (succ zero)) 
y = (succ zero)

succ ((succ (succ zero)) + (succ zero))

x = (succ zero) 
y = (succ zero) 

succ (succ (succ zero + succ zero))

x = zero 
y = succ zero

succ (succ (succ (succ zero))





_+_ : Nat → Nat → Nat
zero + y = y
succ x + y = succ (x + y)

+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+-assoc zero y z = refl
+-assoc (succ x) y z = cong succ (+-assoc x y z) 

x+zero : ∀ (x : Nat) → x ≡ x + zero
x+zero zero = refl
x+zero (succ x) = cong succ (x+zero x)

x+1+y : ∀ x y → x + succ y ≡ succ (x + y)
x+1+y zero y = refl
x+1+y (succ x) y = cong succ (x+1+y x y)

+-comm : ∀ (x y : Nat) → x + y ≡ y + x
+-comm zero y = x+zero y
+-comm (succ x) y = 
  begin
    succ (x + y)
  ≡⟨ cong succ (+-comm x y) ⟩
    succ (y + x)
  ≡⟨ sym (x+1+y y x) ⟩
    y + succ x
  ∎ 
-}
