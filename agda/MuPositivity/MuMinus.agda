--open import Utilities.Logic
open import Utils
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary.Decidable
open import Level

module MuMinus
  (Atom : Set)
  (C : Set)
  (D : Set)
  (Atom : Set)
  (_≼_ : Rel Atom zero)
  (tdoe : DecTotalOrderEq Atom _≼_)
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

open import Assoc (List C) Atom [] _≼_ tdoe

eqAtom : ∀ x y → Dec (x ≡ y)
eqAtom = DecTotalOrderEq._≟_ tdoe


import Database as DB
module DBmodule = DB Atom C eqAtom eqC
open DBmodule public

Interpretation : Set
Interpretation = Assoc

Predicate : Set
Predicate = C → Bool


infixl 21 _⊗_
data Shape : Set where
  v : Atom → Shape
  P : Predicate → Shape
  α[_]_ : (a : C) → Shape → Shape
  _⊗_ : Shape → Shape → Shape
  --_has_ : Shape → ℕ → Shape
  ν : Atom → Shape → Shape
  -_ : Shape → Shape


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
  
  fvs : Shape → List Atom
  fvs (v x) = [ x ] 
  fvs (P x) = []
  fvs (α[ a ] s) = fvs s
  fvs (s ⊗ s₁) = fvs s ∪ fvs s₁
  fvs (ν x s) = fvs s ⊸ x
  fvs (- s) = fvs s

  polarities : Shape → List Atom × List Atom ⊎ ⊤
  polarities (v x) = inj₁ $ [ x ] , []
  polarities (P x) = inj₁ $ [] , []
  polarities (α[ a ] s) = polarities s
  polarities (s ⊗ s₁) with polarities s | polarities s₁
  polarities (s ⊗ s₁) | inj₁ (p₁ , n₁) | inj₁ (p₂ ,  n₂) = inj₁ $ p₁ ∪ p₂ , n₁ ∪ n₂
  polarities (s ⊗ s₁) | inj₁ x | inj₂ tt = inj₂ tt
  polarities (s ⊗ s₁) | inj₂ tt | res₂ = inj₂ tt 
  polarities (ν x s) with polarities s
  polarities (ν x s) | inj₁ (p , n) with x ∈? n
  polarities (ν x s) | inj₁ (p , n) | yes q = inj₂ tt 
  polarities (ν x s) | inj₁ (p , n) | no ¬q = inj₁ (p ⊸ x , n)
  polarities (ν x s) | inj₂ tt = inj₂ tt
  polarities (- s) with polarities s
  polarities (- s) | inj₁ (p , n) = inj₁ (n , p)
  polarities (- s) | inj₂ y = inj₂ tt

  PositiveClosed : Shape → Set
  PositiveClosed s with polarities s
  PositiveClosed s | inj₁ ([] , []) = ⊤
  PositiveClosed s | inj₁ ([] , x ∷ proj₂) = ⊥
  PositiveClosed s | inj₁ (x ∷ proj₁ , proj₂) = ⊥
  PositiveClosed s | inj₂ y = ⊥

  data Polarity : Shape → List Atom → List Atom → Set where
    Var : ∀ {x} → Polarity (v x) [ x ] []
    Prop : ∀ {p} → Polarity (P p) [] []
    Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Nu : ∀ {x s p n} → Polarity s p n → x ∈ p → x ∉ n → Polarity (ν x s) (p ⊸ x) n
    Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p
  
  PositiveIn : Atom → Shape → Set
  PositiveIn a s = ∀ {a p n} → a ∉ n → Polarity s p n

module WFX = FinSet.WF⊂mod C eqC
open WFX hiding (NotInUnionLeft ; NotInUnionRight)

module ModalTransitionSystem (𝓣 : Transitions) where

  S : Subjects
  S = 𝓓 𝓣 ∪ 𝓡 𝓣 
   
  𝓥 : Predicate → Subjects
  𝓥 f = ⟪ s ∈ S ∣ f s ⟫

  {-
  _[_≔_] : Interpretation → Atom → Subjects → Interpretation
  (i [ X ≔ T ]) Y with eqAtom X Y
  (i [ X₁ ≔ T ]) Y | yes p = T
  (i [ X₁ ≔ T ]) Y | no ¬p = i Y

  mapsToSelf : ∀ i S' x → S' ≡ (i [ x ≔ S' ]) x
  mapsToSelf i S' x with eqAtom x x
  mapsToSelf i S' x | yes p = refl
  mapsToSelf i S' x | no ¬p = refl ↯ ¬p
  -} 

  mutual

{-
    gfpWF : (x : Atom) → Shape → (i : Interpretation) → (Acc _⊂_ (i x)) → Subjects
    gfpWF x φ i ac with ⟦ φ ⟧ i
    gfpWF x φ i ac | S' with S' ⊂? (i x)
    gfpWF x φ i (acc rs) | S' | yes p rewrite (mapsToSelf i S' x) =
      let ac = rs ((i [ x ≔ S' ]) x) p
      in gfpWF x φ (i [ x ≔ S' ]) ac
    gfpWF x φ i ac | S' | no ¬p = (i x)

    gfp : Atom → Shape → Interpretation → Subjects
    gfp x φ i = gfpWF x φ (i [ x ≔ S ]) (wf⊂ ((i [ x ≔ S ]) x))
-}

    ⟦_⟧ : Shape → (i : Interpretation) → Subjects
    ⟦ P p ⟧ i = 𝓥 p
    ⟦ α[ a ] φ ⟧ i = ⟪ s ∈ S ∣ Π[ t ∈ S ] ⌊ (s , a , t) ∈trans? 𝓣 ⌋ ⇒ ⌊ t ∈? (⟦ φ ⟧ i) ⌋ ⟫
    ⟦ φ ⊗ φ₁ ⟧ i = (⟦ φ ⟧ i) ∩ (⟦ φ₁ ⟧ i)
    ⟦ ν x φ ⟧ i = gfp x φ i
    ⟦ v x ⟧ i = i ⟨ x ⟩ 
    ⟦ - φ ⟧ i = S ̸ ⟦ φ ⟧ i

    gfpWF : (x : Atom) → (φ : Shape) → (i : Interpretation) → (F : Subjects) → (Acc _⊂_ F) →
      Σ[ R ∈ Subjects ] Σ[ S' ∈ Subjects ] ⟦ φ ⟧ (i [ x ≔ S' ]) ≡ R
    gfpWF x φ i F ac with ⟦ φ ⟧ (i [ x ≔ F ])
    gfpWF x φ i F ac | S' with S' ⊂? F
    gfpWF x φ i F (acc rs) | S' | yes p = gfpWF x φ i S' (rs S' p)
    gfpWF x φ i F ac | S' | no ¬p = ⟦ φ ⟧ (i [ x ≔ S' ]) , S' , refl

    gfp : Atom → Shape → Interpretation → Subjects
    gfp x φ i = proj₁ $ gfpWF x φ i S (wf⊂ S)

    gfpProof : ∀ x φ i →  Σ[ S' ∈ Subjects ] ⟦ φ ⟧ (i [ x ≔ S' ]) ≡ gfp x φ i
    gfpProof x φ i = proj₂ $ gfpWF x φ i S (wf⊂ S) 
    
  open Positivity

  mutual

{-
    Stable : ∀ i X Y →
               (φ : Shape) →  (a x : Atom) → a ≡ x →
      ------------------------------------------------------------
           gfp x φ (i [ a ≔ X ]) ≡ gfp x φ (i [ a ≔ Y ])
    Stable i X Y φ a .a refl = {!!}

    gfpMonotonic : ∀ i X Y {p n} →
      (a x : Atom) → (φ : Shape) → a ∉ n → Polarity φ p n → X ⊆ Y → x ∉ n →
      ------------------------------------------------------------
           gfp x φ (i [ a ≔ X ]) ⊆ gfp x φ (i [ a ≔ Y ])
    gfpMonotonic i X Y a x φ nin pos X⊆Y xnin = {!!} 

    gfpAntitonic : ∀ i X Y {p n} →
      (a x : Atom) → (φ : Shape) → a ∉ p → Polarity φ p n → X ⊆ Y → x ∉ n →
      ------------------------------------------------------------
           gfp x φ (i [ a ≔ Y ]) ⊆ gfp x φ (i [ a ≔ X ])
    gfpAntitonic i X Y a x φ nin pos X⊆Y xnin with Antitone i X Y a φ nin pos X⊆Y
    gfpAntitonic i X Y a x φ nin pos X⊆Y xnin | res = {!res!} 

    gfpAntitonic : ∀ i X Y {p n} →
      (a x : Atom) → (φ : Shape) → a ∉ p → Polarity φ p n → X ⊆ Y → x ∉ n →
           ⟦ φ ⟧ (i [ x ≔ S ]) ⊆ 
           gfp x φ (i [ a ≔ Y ]) ⊆ gfp x φ (i [ a ≔ X ])
      ------------------------------------------------------------
           gfp x φ (i [ a ≔ Y ]) ⊆ gfp x φ (i [ a ≔ X ])
    gfpAntitonic i X Y a x φ nin pos X⊆Y xnin = {!!}
-}

    Monotone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Shape) → a ∉ n → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
            ⟦ φ ⟧ (i [ a ≔ X ]) ⊆ ⟦ φ ⟧ (i [ a ≔ Y ]) 
    Monotone i X Y a (v x) nin pos sub with eqAtom a x
    Monotone i X Y a (v .a) nin pos sub | yes refl
      rewrite Same {a} {a} {Y} i refl | Same {a} {a} {X} i refl = sub
    Monotone i X Y a (v x) nin pos sub | no ¬p
      rewrite Ignore {x} {a} {Y} i (¬p ∘ sym) | Ignore {x} {a} {X} i (¬p ∘ sym) = λ x₁ z → z 
    Monotone i X Y a (P x) nin pos sub = λ x₁ z → z
    Monotone i X Y a (α[ a₁ ] s) nin (Alpha pos) sub =
      WFX.ComprehensionLaw {S} {𝓣 = 𝓣} (Monotone i X Y a s nin pos sub)
    Monotone i X Y a (s ⊗ s₁) nin (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      WFX.IntersectionLaw (Monotone i X Y a s (NotInUnionLeft n₂ nin) pos sub)
                          (Monotone i X Y a s₁ (NotInUnionRight n₁ nin) pos₁ sub)
    Monotone i X Y a (ν x s) nin (Nu pos xinp xnin) sub =
      let res = Monotone i X Y a s nin pos sub
      in λ x₁ x₂ → {!!}
    Monotone i X Y a (- s) nin (Not pos) sub =
      WFX.NegationLaw S (Antitone i X Y a s nin pos sub)
  
    Antitone : ∀ i X Y {p n} →
      (a : Atom) → (φ : Shape) → a ∉ p → Polarity φ p n → X ⊆ Y →
      ---------------------------------------------------
      ⟦ φ ⟧ (i [ a ≔ Y ]) ⊆ ⟦ φ ⟧ (i [ a ≔ X ]) 
    Antitone i X Y a (v x) nip Var sub with eqAtom a x
    Antitone i X Y x (v .x) nip Var sub | yes refl = ⊥-elim $ nip here
    Antitone i X Y a (v x) nip Var sub | no ¬p
      rewrite Ignore {x} {a} {Y} i (¬p ∘ sym) | Ignore {x} {a} {X} i (¬p ∘ sym) = λ x₁ z → z 
    Antitone i X Y a (P x) nip pos sub = λ x₁ z → z
    Antitone i X Y a (α[ a₁ ] s) nip (Alpha pos) sub =
      WFX.ComprehensionLaw {S} {𝓣 = 𝓣} (Antitone i X Y a s nip pos sub)
    Antitone i X Y a (s ⊗ s₁) nip (And {.s} {.s₁} {p₁} {p₂} {n₁} {n₂} pos pos₁) sub =
      WFX.IntersectionLaw (Antitone i X Y a s (NotInUnionLeft p₂ nip) pos sub)
                          (Antitone i X Y a s₁ (NotInUnionRight p₁ nip) pos₁ sub) 
    Antitone i X Y a (ν x s) nip (Nu pos xinp xnin) sub =
      let (S' , p) = gfpProof x s i
      in {!!}
    Antitone i X Y a (- s) nip (Not pos) sub =
      WFX.NegationLaw S (Monotone i X Y a s nip pos sub)
    
{-

_⊢_∶_ : Transitions → X → Shape → Set
𝓣 ⊢ x ∶ φ = x ∈ ⟦ φ ⟧ (λ _ → 𝓓 𝓣 ∪ 𝓡 𝓣) (𝓓 𝓣 ∪ 𝓡 𝓣) 𝓣

checkφ : ∀ 𝓣 x φ → Dec ( 𝓣 ⊢ x ∶ φ )
checkφ 𝓣 x φ = x ∈? ⟦ φ ⟧ (λ _ → (𝓓 𝓣 ∪ 𝓡 𝓣)) (𝓓 𝓣 ∪ 𝓡 𝓣) 𝓣

-}
