module Intro where

open import Level

data ⊥ : Set where

¬ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

proof : ¬ ⊥
proof = λ z → z

notbot : ⊥ → ⊥
notbot ()

data ⊤ : Set where
  tt : ⊤

notnottrue : ¬ (¬ ⊤)
notnottrue p = p tt  -- C-c C-a

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor
    _,_
  field
    π₁ : A
    π₂ : B π₁

syntax Σ A (λ x → B) = ∃[ x ∶ A ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = ∃[ x ∶ A ] B

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A ⊎ B
  inr : (y : B) → A ⊎ B

data ℕ : Set where
  ∅ : ℕ
  1+ : ℕ → ℕ

one = 1+ ∅
two = 1+ one
three = 1+ two

-- C-c C-n

data _≤ℕ_ : ℕ → ℕ → Set where
  ∅≤ : ∀ (n : ℕ) → ∅ ≤ℕ n
  1+≤ : ∀ (n m : ℕ) → n ≤ℕ m → (1+ n) ≤ℕ (1+ m)

_≤ℕdec_ : ∀ x y → (x ≤ℕ y) ⊎ (y ≤ℕ x)
∅ ≤ℕdec y = inl (∅≤ y) -- C-c C-a
1+ x ≤ℕdec ∅ = inr (∅≤ (1+ x))
1+ x ≤ℕdec 1+ y with x ≤ℕdec y
1+ x ≤ℕdec 1+ y | inl p = inl (1+≤ x y p)
1+ x ≤ℕdec 1+ y | inr p = inr (1+≤ y x p)


data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

_≤_ : ℕ → ℕ → 𝔹
∅ ≤ y = true
1+ x ≤ ∅ = false
1+ x ≤ 1+ y = x ≤ y

∥_∥ : 𝔹 → Set
∥ true ∥ = ⊤
∥ false ∥ = ⊥

≤⇒≤ℕ : ∀ x y → ∥ (x ≤ y) ∥ → (x ≤ℕ y)
≤⇒≤ℕ ∅ y p = ∅≤ y
≤⇒≤ℕ (1+ x) ∅ ()
≤⇒≤ℕ (1+ x) (1+ y) p = 1+≤ x y (≤⇒≤ℕ x y p)

≤ℕ⇒≤ : ∀ x y → (x ≤ℕ y) → ∥ (x ≤ y) ∥
≤ℕ⇒≤ .∅ y (∅≤ .y) = tt
≤ℕ⇒≤ .(1+ n) .(1+ m) (1+≤ n m p) = ≤ℕ⇒≤ n m p

data _≡_ {ℓ} {A : Set ℓ} : A → A → Set ℓ where
  refl : ∀ {x} → x ≡ x

data ⟦_⟧ (A : Set) : Set where
  ε : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧

[_] : ∀ {A : Set} → A → ⟦ A ⟧
[ x ] = x ∷ ε

_++_ : ∀ {A : Set} → ⟦ A ⟧ → ⟦ A ⟧ → ⟦ A ⟧
ε ++ y = y
(x ∷ x₁) ++ y = x ∷ (x₁ ++ y)

example : ⟦ ℕ ⟧
example = one ∷ (two ∷ ε)

-- C-c C-n

example2 : ⟦ ℕ ⟧
example2 = example ++ example

-- Decidable TO
record TO (A : Set) : Set₁ where
  constructor
    makeTO
  field
    _≤A_ : A → A → Set
    refl≤ : ∀ x → x ≤A x
    anti≤ : ∀ {x y} → x ≤A y → y ≤A x → x ≡ y
    trans≤ : ∀ {x y z} → x ≤A y → y ≤A z → x ≤A z
    _≤dec_ : ∀ x y → (x ≤A y) ⊎ (y ≤A x)

ℕSorts : TO ℕ
ℕSorts = makeTO _≤ℕ_ refl≤ℕ anti≤ℕ trans≤ℕ _≤ℕdec_
  where refl≤ℕ : (x : ℕ) → x ≤ℕ x
        refl≤ℕ ∅ = ∅≤ ∅
        refl≤ℕ (1+ x) = 1+≤ x x (refl≤ℕ x)
        anti≤ℕ : {x y : ℕ} → x ≤ℕ y → y ≤ℕ x → x ≡ y
        anti≤ℕ (∅≤ .∅) (∅≤ .∅) = refl
        anti≤ℕ (1+≤ n m p) (1+≤ .m .n q) with anti≤ℕ p q
        anti≤ℕ (1+≤ .m m p) (1+≤ .m .m q) | refl = refl
        trans≤ℕ : {x y z : ℕ} → x ≤ℕ y → y ≤ℕ z → x ≤ℕ z
        trans≤ℕ (∅≤ .∅) (∅≤ z) = ∅≤ z
        trans≤ℕ (∅≤ .(1+ n)) (1+≤ n m q) = ∅≤ (1+ m) -- C-c C-a
        trans≤ℕ (1+≤ n m p) (1+≤ .m m₁ q) with trans≤ℕ p q
        trans≤ℕ (1+≤ n m p) (1+≤ .m m₁ q) | res = 1+≤ n m₁ res

