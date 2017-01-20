open import Utils

module FinSet
  where

open import Data.List
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function
open import Data.Unit
open import Data.Sum
open import Membership

open import Induction.WellFounded

ℕ-wf : Well-founded _<′_
ℕ-wf n = acc (aux n)
  where aux : ∀ x y → y <′ x → Acc _<′_ y
        aux .(suc y) y ≤′-refl = ℕ-wf y
        aux .(suc x) y (≤′-step {x} p) = aux x y p 

module WF⊂mod (C : Set) (eq : DecEq C) where

  ∣_∣ : List C → ℕ
  ∣ S ∣ = ∣ S ∣⟨ eq ⟩ 

  open Inverse-image {_<_ = _<′_} (∣_∣) renaming (well-founded to well-founded-ii-obj)
  {- The inverse image of a well founded relation is well founded. -}
 
  _≺_ : List C → List C → Set 
  S ≺ T = S ≺⟨ eq ⟩ T
  
  wf≺ : Well-founded _≺_
  wf≺ = well-founded-ii-obj ℕ-wf

  _⊂_ : List C → List C → Set
  S ⊂ T = S ⊂⟨ eq ⟩ T

  ⊂⇒≺ : ∀ {S T} → S ⊂ T → S ≺ T
  ⊂⇒≺ (proj₁ , proj₂) = proj₂
  
  open Subrelation {_<₁_ = _⊂_} {_<₂_ = _≺_} (⊂⇒≺) renaming (well-founded to well-founded-sub)
  
  wf⊂ : Well-founded _⊂_ 
  wf⊂ = well-founded-sub wf≺

  comprehension-raw : (S : List C) → (P : C → Bool) → List C
  comprehension-raw [] P = [] 
  comprehension-raw (x ∷ S) P = let l = comprehension-raw S P
                                in if P x then (x ∷ l) else l

  ⟪S∣P⟫⊆S : ∀ S P → comprehension-raw S P ⊆ S
  ⟪S∣P⟫⊆S [] P x x∈comprehension = x∈comprehension
  ⟪S∣P⟫⊆S (x ∷ S) P x₁ x∈comprehension with P x
  ⟪S∣P⟫⊆S (x ∷ S) P x₁ x∈comprehension | false = there (⟪S∣P⟫⊆S S P x₁ x∈comprehension)
  ⟪S∣P⟫⊆S (x₁ ∷ S) P .x₁ here | true = here
  ⟪S∣P⟫⊆S (x ∷ S) P x₁ (there x∈comprehension) | true = there (⟪S∣P⟫⊆S S P x₁ x∈comprehension)

  x∈⟪S∣P⟫⇒Px : ∀ x S P → x ∈ comprehension-raw S P → T (P x)
  x∈⟪S∣P⟫⇒Px x [] P ()
  x∈⟪S∣P⟫⇒Px x (x₁ ∷ S) P x∈⟪S∣P⟫ with P x₁ | inspect P x₁
  x∈⟪S∣P⟫⇒Px x (x₁ ∷ S) P x∈⟪S∣P⟫ | false | hide = x∈⟪S∣P⟫⇒Px x S P x∈⟪S∣P⟫ 
  x∈⟪S∣P⟫⇒Px x (.x ∷ S) P here | true | Reveal_·_is_.[ eq₁ ] rewrite eq₁ = tt
  x∈⟪S∣P⟫⇒Px x (x₁ ∷ S) P (there x∈⟪S∣P⟫) | true | hide = x∈⟪S∣P⟫⇒Px x S P x∈⟪S∣P⟫
  
  Px⇒x∈S⇒x∈⟪S∣P⟫ : ∀ S P x → T (P x) → x ∈ S → x ∈ comprehension-raw S P
  Px⇒x∈S⇒x∈⟪S∣P⟫ [] P x₁ TPx x∈S = x∈S
  Px⇒x∈S⇒x∈⟪S∣P⟫ (x₁ ∷ S) P .x₁ TPx here with P x₁
  Px⇒x∈S⇒x∈⟪S∣P⟫ (x₁ ∷ S) P .x₁ () here | false
  Px⇒x∈S⇒x∈⟪S∣P⟫ (x₁ ∷ S) P .x₁ TPx here | true = here
  Px⇒x∈S⇒x∈⟪S∣P⟫ (x ∷ S) P x₁ TPx (there x∈S) with P x
  Px⇒x∈S⇒x∈⟪S∣P⟫ (x ∷ S) P x₁ TPx (there x∈S) | false = Px⇒x∈S⇒x∈⟪S∣P⟫ S P x₁ TPx x∈S
  Px⇒x∈S⇒x∈⟪S∣P⟫ (x ∷ S) P x₁ TPx (there x∈S) | true = there (Px⇒x∈S⇒x∈⟪S∣P⟫ S P x₁ TPx x∈S)
  
  comprehension-syntax : ∀ (S : List C) → (P : C → Bool) → List C
  comprehension-syntax S P = proj₁ (dedup eq (comprehension-raw S P))

  syntax comprehension-raw S (λ x → B) = ⟪ x ∈ S ∣ B ⟫

  _⊂?_ : (S : List C) → (T : List C) → Dec (S ⊂ T)
  S ⊂? T = S ⊂⟨ eq ⟩? T

  _∈?_ : (x : C) → (L : List C) → Dec (x ∈ L)
  x ∈? S = eq2in eq x S

  _∩_ : List C → List C → List C
  S ∩ T = ⟪ s ∈ S ∣ ⌊ s ∈? T ⌋ ⟫

  _̸_ : List C → List C → List C
  S ̸ T = ⟪ s ∈ S ∣ not ⌊ s ∈? T ⌋ ⟫ 

  𝓜 : C → List C → ℕ 
  𝓜 x S = multiplicity eq x S

  _⟶_ : ∀ (P Q : C → Bool) → Set
  P ⟶ Q = ∀ {s : C} → T (P s) → T (Q s)

  BoolImp : ∀ (P Q : C → Bool) → ∀ (s : C) → T (P s ⇒ Q s) → T (P s) → T (Q s)
  BoolImp P Q s Ps⇒Qs Ps with P s | Q s
  BoolImp P Q s Ps⇒Qs () | false | Qs
  BoolImp P Q s () Ps | true | false
  BoolImp P Q s Ps⇒Qs Ps | true | true = tt

  ImpBool : ∀ (P Q : C → Bool) → ∀ (s : C) → (T (P s) → T (Q s)) → T (P s ⇒ Q s) 
  ImpBool P Q s Ps⇒Qs with P s | Q s 
  ImpBool P Q s Ps⇒Qs | false | Qs = tt
  ImpBool P Q s Ps⇒Qs | true | Qs = Ps⇒Qs tt
  
  ImplicationLawRaw : ∀ (S : List C) → (P Q : C → Bool) → P ⟶ Q → comprehension-raw S P ⊆ comprehension-raw S Q 
  ImplicationLawRaw [] P Q imp x ()
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS with ImpBool P Q x (imp {x})
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | ix with P x | Q x
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | ix | false | false = ImplicationLawRaw S P Q imp x₁ inS
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | ix | false | true = there $ ImplicationLawRaw S P Q imp x₁ inS
  ImplicationLawRaw (x ∷ S) P Q imp x₁ inS | () | true | false
  ImplicationLawRaw (x₁ ∷ S) P Q imp .x₁ here | ix | true | true = here
  ImplicationLawRaw (x ∷ S) P Q imp x₁ (there inS) | ix | true | true = there $ ImplicationLawRaw S P Q imp x₁ inS

  ImplicationLaw : ∀ (S : List C) → (P Q : C → Bool) → P ⟶ Q → comprehension-syntax S P ⊆ comprehension-syntax S Q
  ImplicationLaw S P Q imp x inS = dedup-complete eq (comprehension-raw S Q) x (ImplicationLawRaw S P Q imp x (dedup-sound eq (comprehension-raw S P) x inS))

  ComprehensionMonotone : ∀ (S R : List C) → (P Q : C → Bool) → S ⊆ R → P ⟶ Q → comprehension-raw S P ⊆ comprehension-raw R Q
  ComprehensionMonotone S R P Q S⊆R P⟶Q x x∈⟪S∣P⟩ =
    let x∈S = ⟪S∣P⟫⊆S S P x x∈⟪S∣P⟩
        x∈R = S⊆R x x∈S
        Px = x∈⟪S∣P⟫⇒Px x S P x∈⟪S∣P⟩
        Qx = P⟶Q Px 
        x∈⟪R∣Q⟫ = Px⇒x∈S⇒x∈⟪S∣P⟫ R Q x Qx x∈R
     in x∈⟪R∣Q⟫
  
  BothIntersection : ∀ {A B x} → (x ∈ A) → (x ∈ B) → x ∈ (A ∩ B)
  BothIntersection {x ∷ A} {B} here x∈B with x ∈? B
  BothIntersection {x ∷ A} here x∈B | yes p = here
  BothIntersection {x ∷ A} here x∈B | no ¬p = x∈B ↯ ¬p
  BothIntersection {x ∷ A} (there x∈A) x∈B with BothIntersection x∈A x∈B
  BothIntersection {x ∷ A} {B} (there x∈A) x∈B | res with x ∈? B
  BothIntersection {x ∷ A} (there x∈A) x∈B | res | yes p = there res
  BothIntersection {x ∷ A} (there x∈A) x∈B | res | no ¬p = res

  IntersectionBoth : ∀ {A B x} → x ∈ (A ∩ B) → (x ∈ A) × (x ∈ B) 
  IntersectionBoth {[]} ()
  IntersectionBoth {x ∷ A} {B} inboth with x ∈? B
  IntersectionBoth {x ∷ A} here | yes p = here , p
  IntersectionBoth {x ∷ A} (there inboth) | yes p = let x∈A×x∈B = IntersectionBoth {A} inboth
                                                    in there (proj₁ x∈A×x∈B)  , (proj₂ x∈A×x∈B)
  IntersectionBoth {x ∷ A} inboth | no ¬p = let x∈A×x∈B = IntersectionBoth {A} inboth
                                            in there (proj₁ x∈A×x∈B)  , (proj₂ x∈A×x∈B)

  IntersectionLaw : ∀ {A B C D} → A ⊆ B → C ⊆ D → (A ∩ C) ⊆ (B ∩ D)
  IntersectionLaw {A} A⊆B C⊆D x xin =
    let (x∈A , x∈C) = IntersectionBoth {A} xin
    in let x∈B = A⊆B x x∈A
       in let x∈D = C⊆D x x∈C
           in BothIntersection x∈B x∈D 

  IntersectionLeft : ∀ {A B C} → A ⊆ C → (A ∩ B) ⊆ C
  IntersectionLeft {A} A⊆C x x∈A∩B with IntersectionBoth {A} x∈A∩B
  IntersectionLeft A⊆C x x∈A∩B | x∈A , x∈B = A⊆C x x∈A

  IntersectionRight : ∀ {A B C} → B ⊆ C → (A ∩ B) ⊆ C
  IntersectionRight {A} B⊆C x x∈A∩B with IntersectionBoth {A} x∈A∩B
  IntersectionRight B⊆C x x∈A∩B | x∈A , x∈B = B⊆C x x∈B

  BoolSub : ∀ {A B t} → A ⊆ B → T ⌊ t ∈? A ⌋ → T ⌊ t ∈? B ⌋
  BoolSub {A} {B} {t} sub t∈?A with t ∈? A
  BoolSub {A} {B} {t} sub t∈?A | yes p with t ∈? B
  BoolSub sub t∈?A | yes p₁ | yes p = tt
  BoolSub sub t∈?A | yes p | no ¬p = sub _ p ↯ ¬p  
  BoolSub sub () | no ¬p
  
  OrIntroL : ∀ {P R} → T R → T (P ∨ R)
  OrIntroL {R = false} ()
  OrIntroL {false} {true} TR = tt
  OrIntroL {true} {true} TR = tt 

  AndIntro : ∀ {P Q} → T P → T Q → T (P ∧ Q)
  AndIntro {false} Tp Tq = Tp
  AndIntro {true} Tp Tq = Tq

  ImplyAnd : ∀ {P Q R} → (T Q → T R) → T (P ∧ Q) → T (P ∧ R)
  ImplyAnd {false} TQ⇒TR ()
  ImplyAnd {true} TQ⇒TR P∧Q = TQ⇒TR P∧Q

  ImpliesExists : ∀ S P Q → P ⟶ Q → T (any P S) → T (any Q S)
  ImpliesExists [] P Q P⟶Q ∃t∈S = ∃t∈S
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S with P⟶Q {x}
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f with P x
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f | false with ImpliesExists S P Q P⟶Q ∃t∈S 
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f | false | anyS = OrIntroL {Q x} anyS
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f | true with f tt
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f | true | TQx with Q x
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f | true | () | false
  ImpliesExists (x ∷ S) P Q P⟶Q ∃t∈S | f | true | TQx | true = tt

  ImpliesAll : ∀ S P Q → P ⟶ Q → T (all P S) → T (all Q S)
  ImpliesAll [] P Q P⟶Q Πt∈S = tt
  ImpliesAll (x ∷ S) P Q P⟶Q Πt∈S with P⟶Q {x}
  ImpliesAll (x ∷ S) P Q P⟶Q Πt∈S | f with P x
  ImpliesAll (x ∷ S) P Q P⟶Q () | f | false
  ImpliesAll (x ∷ S) P Q P⟶Q Πt∈S | f | true with ImpliesAll S P Q P⟶Q Πt∈S
  ImpliesAll (x ∷ S) P Q P⟶Q Πt∈S | f | true | allS with f tt
  ImpliesAll (x ∷ S) P Q P⟶Q Πt∈S | f | true | allS | TQx = AndIntro TQx allS

  LessEmptyIsEmpty : ∀ {A : List C} → A ⊆ [] → A ≡ []
  LessEmptyIsEmpty {[]} p = refl
  LessEmptyIsEmpty {x ∷ A} p with p x here
  LessEmptyIsEmpty {x ∷ A} p | ()

  NegationLaw : ∀ S {A B} → A ⊆ B → (S ̸ B) ⊆ (S ̸ A)
  NegationLaw [] A⊆B x x∈S̸B = x∈S̸B
  NegationLaw (x ∷ S) {A} {B} A⊆B with x ∈? A
  NegationLaw (x ∷ S) {A} {B} A⊆B | yes p with A⊆B x p
  NegationLaw (x ∷ S) {A} {B} A⊆B | yes p | res with x ∈? B
  NegationLaw (x ∷ S) A⊆B | yes p₁ | res | yes p = NegationLaw S A⊆B
  NegationLaw (x ∷ S) A⊆B | yes p | res | no ¬p = res ↯ ¬p
  NegationLaw (x ∷ S) {A} {B} A⊆B | no ¬p with x ∈? B
  NegationLaw (x ∷ S) A⊆B | no ¬p | yes p = λ y y∈S̸B → there $ NegationLaw S A⊆B y y∈S̸B
  NegationLaw (x ∷ S) A⊆B | no ¬p₁ | no ¬p with NegationLaw S A⊆B
  NegationLaw (x ∷ S) A⊆B | no ¬p₁ | no ¬p | res = λ y y∈S̸B → hereOrThere S A⊆B y∈S̸B
    where hereOrThere : ∀ S {A B x y} → A ⊆ B → y ∈ (x ∷ (S ̸ B)) → y ∈ (x ∷ (S ̸ A))
          hereOrThere S A⊆B here = here
          hereOrThere S A⊆B (there y∈S̸B) = there $ NegationLaw S A⊆B _ y∈S̸B

  open import Database C C eq eq

  ImpliesAbstract : ∀ {P Q R} → T (Q ⇒ R) → T (P ⇒ Q) → T (P ⇒ R)
  ImpliesAbstract {false} Q⇒R P⇒R = tt
  ImpliesAbstract {true} {false} Q⇒R ()
  ImpliesAbstract {true} {true} Q⇒R P⇒R = Q⇒R
