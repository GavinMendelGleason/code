
open import Relation.Binary -- .PropositionalEquality
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_)

module Term (Atom : Set) (_≟_ : Decidable (_≡_ {A = Atom})) where

open import Data.List
open import Relation.Nullary
open import Data.Product
open import Function
open import Data.List.Any

open module M = Membership (PropEq.setoid Atom) public

data Λ : Set where
  var : Atom → Λ
  true : Λ
  false : Λ
  if_then_else_ : Λ → Λ → Λ → Λ
  ƛ : Atom → Λ → Λ
  _·_ : Λ → Λ → Λ

PrimIndΛ : ∀ (P : Λ → Set) →
        ((a : Atom) → P (var a)) →
        (t : P true) → (f : P false) →
        (ifc : {M N O : Λ} → P M → P N → P O → P (if M then N else O))
        (lam : {M : Λ} → (a : Atom) → P M → P (ƛ a M))
        (app : {M N : Λ} → P M → P N → P (M · N)) →
        (t : Λ) → P t
PrimIndΛ P v t f ifc lam app (var x) = v x
PrimIndΛ P v t f ifc lam app true = t
PrimIndΛ P v t f ifc lam app false = f
PrimIndΛ P v t f ifc lam app (if x then x₁ else x₂) =
  ifc (PrimIndΛ P v t f ifc lam app x) 
    (PrimIndΛ P v t f ifc lam app x₁)
    (PrimIndΛ P v t f ifc lam app x₂)
PrimIndΛ P v t f ifc lam app (ƛ x x₁) =
  lam x (PrimIndΛ P v t f ifc lam app x₁)
PrimIndΛ P v t f ifc lam app (x · y) =
  app (PrimIndΛ P v t f ifc lam app x)
    (PrimIndΛ P v t f ifc lam app y)

foldΛ :  ∀ {R : Set} → (v : Atom → R) →
        (t : R) → (f : R) →
        (ifc : R → R → R → R)
        (lam : Atom → R → R)
        (app : R → R → R) → Λ → R
foldΛ {R} v t f ifc lam app =
  PrimIndΛ (λ _ → R)
    v t f
    (λ {_ _ _} → ifc)
    (λ {_} → lam)
    (λ {_ _} → app)

_⊕ₐ_ : Atom → Atom → Atom → Atom
(x ⊕ₐ y) z with z ≟ x
(x ⊕ₐ y) z | yes p = y
(x ⊕ₐ y) z | no ¬p with z ≟ y
(x ⊕ₐ y) z | no ¬p | yes p = x
(x ⊕ₐ y) z | no ¬p₁ | no ¬p = z

_⊕_ : Atom → Atom → Λ → Λ
x ⊕ y =
  foldΛ (var ∘ (x ⊕ₐ y))
    true false if_then_else_ (ƛ ∘ (x ⊕ₐ y)) _·_

Π : Set
Π = List (Atom × Atom)

_●ₐ_ : Π → Atom → Atom
l ●ₐ a = foldr (uncurry (_⊕ₐ_)) a l 

_●_ : Π → Λ → Λ
l ● t = foldr (uncurry (_⊕_)) t l

data _~α_ : Λ → Λ → Set where
  ~αv : {a : Atom} → var a ~α var a
  ~αtrue : true ~α true
  ~αfalse : false ~α false
  ~αif : {M M' N N' O O' : Λ} →  M ~α M' → N ~α N' → O ~α O' → (if M then N else O) ~α (if M' then N' else O')
  ~α· : {M M' N N' : Λ} → M ~α M' → N ~α N' → (M · N) ~α (M' · N')
  ~αƛ : {M M' : Λ} {a b : Atom} {xs : List Atom} → ((c : Atom) → (c ∉ xs) → ((a ⊕ c) M) ~α ((b ⊕ c) M') → (ƛ a M) ~α (ƛ b M'))

IndPermΛ : (P : Λ → Set) →
        ((a : Atom) → P (var a)) →
        (t : P true) → (f : P false) →
        (ifc : {M N O : Λ} → P M → P N → P O → P (if M then N else O))
        (lam : {M : Λ} (a : Atom) → (∀ π → P (π ● M)) → P (ƛ a M))
        (app : {M N : Λ} → P M → P N → P (M · N)) →
        (t : Λ) → P t
IndPermΛ P v t f ifc lam app (var x) = v x
IndPermΛ P v t f ifc lam app true = t
IndPermΛ P v t f ifc lam app false = f
IndPermΛ P v t f ifc lam app (if x then x₁ else x₂) =
  ifc (IndPermΛ P v t f ifc lam app x) 
    (IndPermΛ P v t f ifc lam app x₁)
    (IndPermΛ P v t f ifc lam app x₂)
IndPermΛ P v t f ifc lam app (ƛ x x₁) =
  lam x (λ π → PrimIndΛ P v t f ifc (λ a x₂ → {!lam a!}) app (π ● x₁))
IndPermΛ P v t f ifc lam app (x · y) =
  app (IndPermΛ P v t f ifc lam app x)
    (IndPermΛ P v t f ifc lam app y)
  
-- Beneficiary accnt #
