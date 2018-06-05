{-
======================================
=== THE GREAT RESURRECTION OF PROP ===
======================================

Bringing back the impredicative sort Prop of definitionally proof-irrelevant propositions to Agda.

To check this file, get the prop-rezz branch of Agda at https://github.com/jespercockx/agda/tree/prop-rezz.

This file is a short demo meant to show what you currently can (and can't) do with Prop.
-}

-- You need the following flag to enable (definitional) proof irrelevance for types in Prop.
{-# OPTIONS --proof-irrelevance  #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- You can define datatypes in Prop, even with multiple constructors.
-- However, all constructors are considered (definitionally) equal.
data TestProp : Prop where
  p₁ p₂ : TestProp
  -- ^ p₁ ≡ p₂

-- Pattern matching on a datatype in Prop is disallowed ...
-- toBool : TestProp → Bool
-- toBool p₁ = true
-- toBool p₂ = false
--
-- Error:
-- Cannot split on type in Prop unless target is Prop as well
-- when checking that the pattern p₁ has type TestProp

-- ... unless the target type is a Prop:
test-case : {P : Prop} (x₁ x₂ : P) → TestProp → P
test-case x₁ x₂ p₁ = x₁
test-case x₁ x₂ p₂ = x₂

-- Since Prop is not included in the universe hierarchy @Set ℓ@, we cannot
-- use universe-polymorphic definitions at Prop. To consider equality at
-- types in Prop, we instead have to redefine equality at @A : Prop@:
data _≡Prop_ {A : Prop} (x : A) : A → Set where
  refl : x ≡Prop x

-- All elements of a Prop are definitionally equal:
p₁≡p₂ : p₁ ≡Prop p₂
p₁≡p₂ = refl

-- Consequentially, constructors are not disjoint:
-- p₁≢p₂ : {P : Prop} → p₁ ≡Prop p₂ → P
-- p₁≢p₂ ()

-- Error:
-- p₁ ≡Prop p₂ should be empty, but the following constructor patterns
-- are valid:
--   refl
-- when checking that the clause p₁≢p₂ () has type
-- {P : Prop} → p₁ ≡Prop p₂ → P

-- A special case are empty types in Prop: these can be eliminated to
-- any other type.
data ⊥ : Prop where

absurd : {A : Set} → ⊥ → A
absurd ()

-- We can also define record types in Prop, such as the unit:
record ⊤ : Prop  where
  constructor tt

-- Fields of a record in Prop don't have to be in Prop themselves.
-- If they aren't, they are implicitly squashed:
record Squash (A : Set) : Prop where
  constructor squash
  field unsquash : A
open Squash

-- It's not possible to get a squashed field out by pattern matching:
-- desquash : ∀ {A : Set} → Squash A → A
-- desquash (squash x) = x
--
-- Error:
-- Cannot split on type in Prop unless target is Prop as well
-- when checking that the pattern squash x has type Squash A

-- Projections from a Prop record are considered irrelevant:
-- unsquasher : ∀ {A : Set} → Squash A → A
-- unsquasher = unsquash
--
-- Error:
-- Identifier unsquash is declared irrelevant, so it cannot be used
-- here
-- when checking that the expression unsquash has type Squash .A → .A

-- This is also disallowed:
-- squashily : ∀ {A : Set} {x y : A} → squash x ≡Prop squash y → x ≡ y
-- squashily refl = refl
--
-- Error:
-- .x != .y of type .A
-- when checking that the expression refl has type .x ≡ .y


-- To use the projection, we need to be in the process of constructing a Prop
-- (or an irrelevant argument):
desquashify : {A : Set} {P : Prop} → (A → P) → Squash A → P
desquashify f x = f (unsquash x)

-- Prop is impredicative, so we can do some fun things:
True : Prop
True = {P : Prop} → P → P

False : Prop
False = {P : Prop} → P

-- We have Prop : Set₀, so we can store predicates in a small datatype:
data NatProp : Set where
  c : (Nat → Prop) → NatProp

-- To define more interesting predicates, we need to define them by pattern matching:
_≤_ : Nat → Nat → Prop
zero  ≤ y     = ⊤
suc x ≤ suc y = x ≤ y
_     ≤ _     = ⊥

-- We can also define the induction principle for predicates defined in this way,
-- using the fact that we can eliminate absurd propositions with a () pattern.
≤-ind : (P : (m n : Nat) → Set)
      → (pzy : (y : Nat) → P zero y)
      → (pss : (x y : Nat) → P x y → P (suc x) (suc y))
      → (m n : Nat) → m ≤ n → P m n
≤-ind P pzy pss zero y pf = pzy y
≤-ind P pzy pss (suc x) (suc y) pf = pss x y (≤-ind P pzy pss x y pf)
≤-ind P pzy pss (suc _) zero ()

-- Trying to define ≤ as a datatype in Prop doesn't work very well:
data _≤'_ : Nat → Nat → Prop where
  zero : (y : Nat) → zero ≤' y
  suc  : (x y : Nat) → x ≤' y → suc x ≤' suc y

-- ≤'-ind : (P : (m n : Nat) → Set)
--        → (pzy : (y : Nat) → P zero y)
--        → (pss : (x y : Nat) → P x y → P (suc x) (suc y))
--        → (m n : Nat) → m ≤' n → P m n
-- ≤'-ind P pzy pss .0 y (zero .y) = ?
-- ≤'-ind P pzy pss .(suc x) .(suc y) (suc x y pf) = ?

-- Error:
-- Cannot split on type in Prop unless target is Prop as well
-- when checking that the pattern zero .y has type m ≤' y

-- We can define equality as a Prop, but (currently) we cannot define
-- the corresponding eliminator, so the equality is only useful for
-- refuting impossible equations.
data _≡P_ {A : Set} (x : A) : A → Prop where
  refl : x ≡P x

0≢1 : 0 ≡P 1 → ⊥
0≢1 ()

-- J-P : {A : Set} (x : A) (P : (y : A) → x ≡P y → Set)
--     → P x refl → (y : A) (e : x ≡P y) → P y e
-- J-P x P p .x refl = p

-- Error:
-- Cannot split on type in Prop unless target is Prop as well
-- when checking that the pattern refl has type x ≡P y
