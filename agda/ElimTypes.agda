module ElimTypes where 

open import Level

data ⊥ {ℓ} : Set ℓ where 
  
data ⊤ {ℓ} : Set ℓ where 
  tt : ⊤

data ℕ : Set where 
  z : ℕ 
  s : ℕ → ℕ

one = (s z) 
two = (s one) 
three = (s two)

_+_ : ℕ → ℕ → ℕ 
z + y = y
s x + y = s (x + y) 

data 𝔹 : Set where 
  true : 𝔹 
  false : 𝔹 

_≡ℕ_ : ℕ → ℕ → 𝔹
z ≡ℕ z = true
z ≡ℕ s y = false
s x ≡ℕ z = false
s x ≡ℕ s y = x ≡ℕ y

record Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where 
  constructor 
    _,_
  field 
    π₁ : A
    π₂ : B π₁

_×_ : Set → Set → Set 
A × B = Σ A (λ _ -> B)

Vec : ℕ → Set → Set 
Vec z A = ⊤ 
Vec (s n) A = A × Vec n A

nil : (A : Set) → Vec z A 
nil = λ A → tt 

cons : (A : Set) → (n : ℕ) → A → Vec n A → Vec (s n) A
cons A n x v = x , v

example : Vec two ℕ 
example = (cons ℕ _ one (cons ℕ _ two (nil ℕ)))

if_then_else_ : ∀ {ℓ} {C : Set ℓ} → 𝔹 → C → C → C 
if b then c else d = {!!}

In : ∀ {ℓ} {n : ℕ} → ℕ → Vec n ℕ → Set ℓ
In {ℓ} {z} x v = ⊥
In {ℓ} {s n} x (y , v) = if (x ≡ℕ y) then ⊤ else In y v

_++_ : {A : Set} → {n m : ℕ} → Vec n A → Vec m A → Vec (n + m) A
_++_ {A} {z} {m} xs ys = ys
_++_ {A} {s n} {m} (π₁ , π₂) ys = cons A (n + m) π₁ (π₂ ++ ys) 

--weakening : ∀ {A a} (as bs cs : Vec A) → 
--    (a \u2208 (as ++ cs)) \u2192 (a \u2208 (as ++ bs ++ cs))
