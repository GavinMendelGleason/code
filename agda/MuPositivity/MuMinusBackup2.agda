open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable

module MuMinus
  (Atom : Set)
  (C : Set)
  (D : Set)
  (eqAtom : DecEq Atom)
  (eqC : DecEq C)
  where

open import Relation.Binary.PropositionalEquality hiding (inspect ; [_])
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Function
open import Data.Bool hiding (_≟_)
open import Data.List
open import Induction.WellFounded
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import FinSet
open import Membership

import Database as DB
module DBmodule = DB Atom C eqAtom eqC
open DBmodule public

Interpretation : Set
Interpretation = Atom → Subjects

Predicate : Set
Predicate = C → Bool

module WFX = FinSet.WF⊂mod C eqC
open WFX hiding (NotInUnionLeft ; NotInUnionRight)

module ModalTransitionSystem (𝓣 : Transitions) where

  S : Subjects
  S = 𝓓 𝓣 ∪ 𝓡 𝓣 
   
  𝓥 : Predicate → Subjects
  𝓥 f = ⟪ s ∈ S ∣ f s ⟫

  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  Monotone : (Interpretation → Subjects → Subjects) → Set
  Monotone f = ∀ {X Y} → X ⊆ Y → ∀ i → (f i X) ⊆ (f i Y)

  mapsToSelf : ∀ i S' x → S' ≡ (i [ x ≔ S' ]) x
  mapsToSelf i S' x with eqAtom x x
  mapsToSelf i S' x | yes p = refl
  mapsToSelf i S' x | no ¬p = refl ↯ ¬p

  mutual

  
    infixl 21 _⊗_
    data Φ : Set where
      v : Atom → Φ
      P : Predicate → Φ
      α[_]_ : (a : C) → Φ → Φ
      _⊗_ : Φ → Φ → Φ
      ν : ∀ {X Y : Subjects} → (f : Interpretation → Subjects → Subjects) → (M : Monotone f) → Φ
      -_ : Φ → Φ

    fixWF : (i : Interpretation) → (f : Interpretation → Subjects → Subjects) →
            Monotone f → (F : Subjects) → (Acc _⊂_ F) → Σ[ S ∈ Subjects ] S ≈ f i S
    fixWF i f M F ac with f i F
    fixWF i f M F ac | S' with S' ⊂? F 
    fixWF i f M F (acc rs) | S' | yes p = fixWF i f M S' (rs S' p)
    fixWF i f M F ac | S' | no ¬p = {!¬p!} -- (f i S') , ({!!} , (λ x x₁ → {!¬p!})) 
    
    fix : Interpretation → (f : Interpretation → Subjects → Subjects) → Monotone f → Subjects
    fix i f M = proj₁ (fixWF i f M S (wf⊂ S))

    ⟦_⟧ : Φ → (i : Interpretation) → Subjects
    ⟦ P p ⟧ i = 𝓥 p
    ⟦ α[ a ] φ ⟧ i = ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i) ⌋ ⟫
    ⟦ φ ⊗ φ₁ ⟧ i = (⟦ φ ⟧ i) ∩ (⟦ φ₁ ⟧ i)
    ⟦ v x ⟧ i = i x
    ⟦ ν f M ⟧ i = fix i f M
    ⟦ - φ ⟧ i = S ̸ ⟦ φ ⟧ i

    gfpWF : (x : Atom) → (φ : Φ) → (i : Interpretation) → (F : Subjects) → (Acc _⊂_ F) →
      Σ[ R ∈ Subjects ] Σ[ S' ∈ Subjects ] ⟦ φ ⟧ (i [ x ≔ S' ]) ≡ R
    gfpWF x φ i F ac with ⟦ φ ⟧ (i [ x ≔ F ])
    gfpWF x φ i F ac | S' with S' ⊂? F
    gfpWF x φ i F (acc rs) | S' | yes p = gfpWF x φ i S' (rs S' p)
    gfpWF x φ i F ac | S' | no ¬p = ⟦ φ ⟧ (i [ x ≔ S' ]) , S' , refl

    gfp : Atom → Φ → Interpretation → Subjects
    gfp x φ i = proj₁ $ gfpWF x φ i S (wf⊂ S) -- 

    gfpProof : ∀ x φ i →  Σ[ S' ∈ Subjects ] ⟦ φ ⟧ (i [ x ≔ S' ]) ≡ gfp x φ i
    gfpProof x φ i = proj₂ $ gfpWF x φ i S (wf⊂ S) 



{-
module Positivity where
  module WFAtom = FinSet.WF⊂mod Atom eqAtom
  open WFAtom public
  open import Four

  _∈atom?_ : (x : Atom) → (L : List Atom) → Dec (x ∈ L)
  x ∈atom? S = eq2in eqAtom x S

  _⊸_ : List Atom → Atom → List Atom
  _⊸_ X x = ⟪ y ∈ X ∣ not ⌊ (eqAtom x y) ⌋ ⟫ 

  NotInToNeq : ∀ {p x a} → x ∈ p → a ∉ (p ⊸ x) → x ≢ a ⊎ a ∈ p
  NotInToNeq {[]} () a∉p⊸x
  NotInToNeq {y ∷ p} {x} x∈p a∉p⊸x with eqAtom x y
  NotInToNeq {y ∷ p₁} x∈p a∉p⊸x | yes refl = {!!}
  NotInToNeq {y ∷ p} x∈p a∉p⊸x | no ¬p = {!!} 
  
  fvs : Φ → List Atom
  fvs (v x) = [ x ] 
  fvs (P x) = []
  fvs (α[ a ] s) = fvs s
  fvs (s ⊗ s₁) = fvs s ∪ fvs s₁
  --fvs (ν x s) = fvs s ⊸ x
  fvs (- s) = fvs s

  polarities : Φ → List Atom × List Atom ⊎ ⊤
  polarities (v x) = inj₁ $ [ x ] , []
  polarities (P x) = inj₁ $ [] , []
  polarities (α[ a ] s) = polarities s
  polarities (s ⊗ s₁) with polarities s | polarities s₁
  polarities (s ⊗ s₁) | inj₁ (p₁ , n₁) | inj₁ (p₂ ,  n₂) = inj₁ $ p₁ ∪ p₂ , n₁ ∪ n₂
  polarities (s ⊗ s₁) | inj₁ x | inj₂ tt = inj₂ tt
  polarities (s ⊗ s₁) | inj₂ tt | res₂ = inj₂ tt 
  polarities (- s) with polarities s
  polarities (- s) | inj₁ (p , n) = inj₁ (n , p)
  polarities (- s) | inj₂ y = inj₂ tt

  PositiveClosed : Φ → Set
  PositiveClosed s with polarities s
  PositiveClosed s | inj₁ ([] , []) = ⊤
  PositiveClosed s | inj₁ ([] , x ∷ proj₂) = ⊥
  PositiveClosed s | inj₁ (x ∷ proj₁ , proj₂) = ⊥
  PositiveClosed s | inj₂ y = ⊥

  data Polarity : Φ → List Atom → List Atom → Set where
    Var : ∀ {x} → Polarity (v x) [ x ] []
    Prop : ∀ {p} → Polarity (P p) [] []
    Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p
  
  PositiveIn : Atom → Φ → Set
  PositiveIn a s = ∀ {a p n} → a ∉ n → Polarity s p n

  open Positivity

  mutual

    Monotone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ) → a ∉ n → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
            ⟦ φ ⟧ (i [ a ≔ X ]) ⊆ ⟦ φ ⟧ (i [ a ≔ Y ]) 
    Monotone i X Y a (v x) nin pos sub with eqAtom a x
    Monotone i X Y a (v .a) nin pos sub | yes refl = sub
    Monotone i X Y a (v x) nin pos sub | no ¬p = λ x₁ z → z
    Monotone i X Y a (P x) nin pos sub = λ x₁ z → z
    Monotone i X Y a (α[ a₁ ] s) nin (Alpha pos) sub =
      WFX.ComprehensionLaw {S} {𝓣 = 𝓣} (Monotone i X Y a s nin pos sub)
    Monotone i X Y a (s ⊗ s₁) nin (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      WFX.IntersectionLaw (Monotone i X Y a s (NotInUnionLeft n₂ nin) pos sub)
                          (Monotone i X Y a s₁ (NotInUnionRight n₁ nin) pos₁ sub)
    Monotone i X Y a (- s) nin (Not pos) sub =
      WFX.NegationLaw S (Antitone i X Y a s nin pos sub)
  
    Antitone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Φ) → a ∉ p → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
      ⟦ φ ⟧ (i [ a ≔ Y ]) ⊆ ⟦ φ ⟧ (i [ a ≔ X ]) 
    Antitone i X Y a (v x) nip Var sub with eqAtom a x
    Antitone i X Y x (v .x) nip Var sub | yes refl = ⊥-elim $ nip here
    Antitone i X Y a (v x) nip Var sub | no ¬p = λ x₁ z → z
    Antitone i X Y a (P x) nip pos sub = λ x₁ z → z
    Antitone i X Y a (α[ a₁ ] s) nip (Alpha pos) sub =
      WFX.ComprehensionLaw {S} {𝓣 = 𝓣} (Antitone i X Y a s nip pos sub)
    Antitone i X Y a (s ⊗ s₁) nip (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      WFX.IntersectionLaw (Antitone i X Y a s (NotInUnionLeft p₂ nip) pos sub)
                          (Antitone i X Y a s₁ (NotInUnionRight p₁ nip) pos₁ sub) 
    Antitone i X Y a (- s) nip (Not pos) sub =
      WFX.NegationLaw S (Monotone i X Y a s nip pos sub)
-}
