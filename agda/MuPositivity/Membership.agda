module Membership where

open import Utils
open import Data.List
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Relation.Binary hiding (_⇒_)
open import Data.Product
open import Data.Nat hiding (_∸_)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function
open import Data.Sum

data _∈_  {C : Set} : (x : C) → (L : List C) → Set where
  here : ∀ {x L} → x ∈ (x ∷ L)
  there : ∀ {x y L} → x ∈ L → x ∈ (y ∷ L)

_∉_ : ∀ {C : Set} → C → List C → Set
x ∉ S = x ∈ S → ⊥

eq2in : ∀ {C : Set} → (eq : DecEq C) → (x : C) → (L : List C) → Dec (x ∈ L)
eq2in eq₁ x [] = no (λ ())
eq2in eq₁ x (x₁ ∷ L) with eq2in eq₁ x L
eq2in eq₁ x (x₁ ∷ L) | yes p = yes (there p)
eq2in eq₁ x (x₁ ∷ L) | no ¬p with eq₁ x x₁
eq2in eq₁ x (.x ∷ L) | no ¬p | yes refl = yes here
eq2in eq₁ x (x₁ ∷ L) | no ¬p₁ | no ¬p = no (aux ¬p₁ ¬p)
  where aux : ∀ {C} {x x₁ : C} {L} → x ∉ L → x ≢ x₁ → x ∉ (x₁ ∷ L)
        aux p q here = q refl
        aux p q (there r) = p r

DecIn : ∀ (X : Set) → Set
DecIn X = ∀ (x : X) (L : List X) → Dec (x ∈ L)

data _#_ {C} : C → List C → Set where
  []# : ∀ {x} → x # []
  snoc# : ∀ {x y L} → x # L → y ≢ x → x # (y ∷ L)

#? : ∀ {C : Set} (eq : DecEq C) → Decidable (_#_ {C})
#? eq x [] = yes []#
#? eq x₁ (x ∷ L) with #? eq x₁ L
#? eq x₁ (x ∷ L) | yes p with eq x x₁
#? eq x₁ (.x₁ ∷ L) | yes p₁ | yes refl = no (λ {(snoc# L#x₁ q) → q refl})
#? eq x₁ (x ∷ L) | yes p | no ¬p = yes (snoc# p ¬p)
#? eq x₁ (x ∷ L) | no ¬p = no (λ { (snoc# L#x₁ q) → ¬p L#x₁})

∉⇒# : ∀ {C} → (eq : DecEq C) → ∀ xs (x : C) → x ∉ xs → x # xs
∉⇒# eq [] x p = []#
∉⇒# eq (x ∷ xs) x₁ p with eq x₁ x
∉⇒# eq (x ∷ xs) .x p₁ | yes refl = ⊥-elim (p₁ here)
∉⇒# eq (x ∷ xs) x₁ p | no ¬p with ∉⇒# eq xs x₁ (λ z → p (there z))
∉⇒# eq (x ∷ xs) x₁ p | no ¬p | q = snoc# q (¬p ∘ sym)

∈∧#⇒⊥ : ∀ {C} {xs} {x : C} → x # xs → x ∈ xs → ⊥
∈∧#⇒⊥ []# ()
∈∧#⇒⊥ (snoc# x#L x₁) here = x₁ refl
∈∧#⇒⊥ (snoc# x#L x₁) (there x∈xs) = ∈∧#⇒⊥ x#L x∈xs

#-lemma : ∀ {C} → (eq : DecEq C) → ∀ (x y : C) xs → y ∉ xs → y ∈ (x ∷ xs) → x # xs → x ≡ y
#-lemma eq x y xs p q r with ∉⇒# eq xs y p
#-lemma eq y .y xs p here r | res = refl
#-lemma eq x y xs p (there q) r | res = q ↯ p

#-lemma₁ : ∀ {C} → (eq : DecEq C) → ∀ (x y : C) xs → x # xs → (x # (y ∷ xs) → ⊥) → x ≡ y
#-lemma₁ eq x y xs p q with eq x y
#-lemma₁ eq x .x xs p₁ q | yes refl = refl
#-lemma₁ eq x y xs p q | no ¬p = let h = snoc# p (¬p ∘ sym) in h ↯ q

¬#⇒∈ : ∀ {C} → (eq : DecEq C) → ∀ xs (x : C) → (x # xs → ⊥) → x ∈ xs
¬#⇒∈ eq [] x p = ⊥-elim (p []#)
¬#⇒∈ eq (x ∷ xs) x₁ p with #? eq x₁ xs
¬#⇒∈ eq (x ∷ xs) x₁ p₁ | yes p with #-lemma₁ eq x₁ x xs p p₁
¬#⇒∈ eq (x ∷ xs) .x p₁ | yes p | refl = here
¬#⇒∈ eq (x ∷ xs) x₁ p | no ¬p with ¬#⇒∈ eq xs x₁ ¬p
¬#⇒∈ eq (x ∷ xs) x₁ p | no ¬p | res = there res

_⊆_ : ∀ {C : Set} (xs ys : List C) → Set
S ⊆ T = ∀ x → x ∈ S → x ∈ T

{- Properties of subset -}
⊆-trans : ∀ {C : Set} {S T U : List C} → S ⊆ T → T ⊆ U → S ⊆ U
⊆-trans S⊆T T⊆U x x∈S = T⊆U x (S⊆T x x∈S)

¬x∷S⊆T⇒x∉T⇒S⊆T : ∀ {C : Set} {S T : List C} {x} → ¬ (x ∷ S) ⊆ T → x ∈ T  → ¬ S ⊆ T
¬x∷S⊆T⇒x∉T⇒S⊆T ¬x∷S⊆T x∈T S⊆T = ¬x∷S⊆T (λ {_ here → x∈T ; y (there y∈S) → S⊆T y y∈S})

¬⊆⇒∃x : ∀ {C : Set} {S T : List C} (eq : DecEq C) → ¬ S ⊆ T → Σ[ x ∈ C ] x ∈ S × x ∉ T
¬⊆⇒∃x {S = []} eq ¬S⊆T = ⊥-elim (¬S⊆T (λ x → λ ()))
¬⊆⇒∃x {S = x ∷ S} {T = T} eq ¬S⊆T with eq2in eq x T
¬⊆⇒∃x {C} {x ∷ S} eq ¬S⊆T | yes p =
  let (x , x∈S , x∉T) = ¬⊆⇒∃x {S = S} eq (¬x∷S⊆T⇒x∉T⇒S⊆T ¬S⊆T p)
  in x , there x∈S , x∉T
¬⊆⇒∃x {C} {x ∷ S} eq ¬S⊆T | no ¬p = x , here , ¬p

_⊆⟨_⟩?_ : ∀ {C : Set} (xs : List C) (eq : DecEq C) (ys : List C) → Dec (xs ⊆ ys)
[] ⊆⟨ eq ⟩? T = yes (λ x → λ ())
(x ∷ S) ⊆⟨ eq ⟩? T with S ⊆⟨ eq ⟩? T
(x ∷ S) ⊆⟨ eq ⟩? T | yes p with eq2in eq x T
(x ∷ S) ⊆⟨ eq ⟩? T | yes p₁ | yes p = yes (λ x₁ x₂ → aux p x₂ p₁)
  where aux : ∀ {C : Set} {T S : List C} {x y : C} → x ∈ T → y ∈ (x ∷ S) → S ⊆ T → y ∈ T
        aux P here R = P
        aux P (there Q) R = R _ Q
(x ∷ S) ⊆⟨ eq ⟩? T | yes p | no ¬p = no (λ z → ¬p (z x here))
(x ∷ S) ⊆⟨ eq ⟩? T | no ¬p = no (λ z → ¬p (λ x₁ z₁ → z x₁ (there z₁)))

_≈_ : ∀ {C : Set} (xs ys : List C) → Set
S ≈ T = S ⊆ T × T ⊆ S

data NoDup {C : Set} : List C → Set where
  [] : NoDup []
  _∷_ : ∀ {x L} → x # L → NoDup L → NoDup (x ∷ L)

dedup : ∀ {C : Set} → (eq : DecEq C) → (L : List C) → Σ[ S ∈ List C ] NoDup S
dedup eq [] = [] , []
dedup eq (x ∷ L) with dedup eq L
dedup eq (x ∷ L) | L' , P with #? eq x L'
dedup eq (x ∷ L) | L' , P | yes p = x ∷ L' , p ∷ P
dedup eq (x ∷ L) | L' , P | no ¬p = L' , P

dedup-sound : ∀ {C} → (eq : DecEq C) → ∀ xs y → y ∈ proj₁ (dedup eq xs) → y ∈ xs
dedup-sound eq [] y y∈dedup = y∈dedup
dedup-sound eq (x ∷ xs) y y∈dedup with dedup eq xs | dedup-sound eq xs y
dedup-sound eq (x ∷ xs) y y∈dedup | S , P | Q with #? eq x S
dedup-sound eq (y ∷ xs) .y here | S , P | Q | yes p = here
dedup-sound eq (x ∷ xs) y (there y∈dedup) | S , P | Q | yes p = there (Q y∈dedup)
dedup-sound eq (x ∷ xs) y y∈dedup | S , P | Q | no ¬p = there (Q y∈dedup)

dedup-complete : ∀ {C} → (eq : DecEq C) → ∀ xs y → y ∈ xs → y ∈ proj₁ (dedup eq xs)
dedup-complete eq [] y y∈xs = y∈xs
dedup-complete eq (x ∷ xs) y y∈xs with dedup eq xs | dedup-complete eq xs y
dedup-complete eq (x ∷ xs) y y∈xs | S , P | Q with #? eq x S
dedup-complete eq (y ∷ xs) .y here | S , P | Q | yes p = here
dedup-complete eq (x ∷ xs) y (there y∈xs) | S , P | Q | yes p = there (Q y∈xs)
dedup-complete eq (y ∷ xs) .y here | S , P | Q | no ¬p = ¬#⇒∈ eq S y ¬p
dedup-complete eq (x ∷ xs) y (there y∈xs) | S , P | Q | no ¬p = Q y∈xs

dedup-idem : ∀ {C} → (eq : DecEq C) → ∀ xs → NoDup xs → proj₁ (dedup eq xs) ≡ xs
dedup-idem eq .[] [] = refl
dedup-idem eq (_ ∷ L) (x₁ ∷ ndxs) with dedup eq L | dedup-idem eq L ndxs
dedup-idem eq (x ∷ L) (x₁ ∷ ndxs) | A , ndA | dedup-eq with #? eq x A
dedup-idem eq (x ∷ .A) (x₁ ∷ ndxs) | A , ndA | refl | (yes p) = refl
dedup-idem eq (x ∷ L) (x₁ ∷ ndxs) | A , ndA | refl | (no ¬p) = ⊥-elim (¬p x₁)

dedup-≈ : ∀ {C} → ∀ xs (eq : DecEq C) → proj₁ (dedup eq xs) ≈ xs
dedup-≈ xs eq = dedup-sound eq xs , dedup-complete eq xs

∣_∣⟨_⟩ : {C : Set} → List C → (eq : DecEq C) → ℕ
∣ S ∣⟨ eq ⟩ = length (proj₁ (dedup eq S))

multiplicity : {C : Set} → (eq : DecEq C) → C → List C → ℕ
multiplicity eq x [] = zero
multiplicity eq x (x₁ ∷ L) with eq x x₁
multiplicity eq x (x₁ ∷ L) | yes p = suc (multiplicity eq x L)
multiplicity eq x (x₁ ∷ L) | no ¬p = multiplicity eq x L

open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool hiding (_≟_ ; _<?_ )

remove : ∀ {C} (eq : DecEq C) → C → List C → List C
remove eq x M = filter (eq x) M

remove-is-gone : ∀ {C} (eq : DecEq C) x M → x ∉ remove eq x M
remove-is-gone eq x [] = λ ()
remove-is-gone eq x (x₁ ∷ M) with remove-is-gone eq x M
remove-is-gone eq x (x₁ ∷ M) | res with eq x x₁
remove-is-gone eq x (x₁ ∷ M) | res | eqxx₁ with does (eq x x₁)
remove-is-gone eq x (x ∷ M) | res | .true because ofʸ refl | false = ?
remove-is-gone eq x (x ∷ M) | res | .true because ofʸ refl | true = ?
remove-is-gone eq x (x₁ ∷ M) | res | .false because ofⁿ ¬p | doeseqxx₁ = {!!}
  where mustbethere : ∀ {C} (x : C) x₁ P → x ≢ x₁ → x ∉ P → x ∈ (x₁ ∷ P) → ⊥
        mustbethere x .x P p x∉P here = p refl
        mustbethere x x₁ P p x∉P (there x∈x₁) = x∉P x∈x₁

remove-is-convervative : ∀ {C} (eq : DecEq C) x y M → x ≢ y → y ∈ M → y ∈ remove eq x M
remove-is-convervative eq x y [] p y∈M = y∈M
remove-is-convervative eq x y (.y ∷ M) p here with eq x y
remove-is-convervative eq x y (.y ∷ M) p₁ here | yes p = p ↯ p₁
remove-is-convervative eq x y (.y ∷ M) p here | no ¬p = {!!} -- here
remove-is-convervative eq x y (x₁ ∷ M) p (there y∈M) with eq x x₁
remove-is-convervative eq x₁ y (.x₁ ∷ M) p₁ (there y∈M) | yes refl =
  {!!} -- remove-is-convervative eq x₁ y M p₁ y∈M
remove-is-convervative eq x y (x₁ ∷ M) p (there y∈M) | no ¬p =
  {!!} -- there (remove-is-convervative eq x y M p y∈M)

remove⇒appart : ∀ {C} (eq : DecEq C) x L → x # remove eq x L
remove⇒appart eq x [] = []#
remove⇒appart eq x (y ∷ L) with eq x y
remove⇒appart eq x (.x ∷ L) | yes refl = {!!} -- remove⇒appart eq x L
remove⇒appart eq x (y ∷ L) | no ¬p = {!!} -- snoc# (remove⇒appart eq x L) (¬p ∘ sym)

-- remove-appart-stable : ∀ {C} (eq : DecEq C) {x L} → x # L → L ≡ remove eq x L
-- remove-appart-stable eq []# = refl
-- remove-appart-stable eq {a} (snoc# {C} {x} {y} x#L x₁) with eq a x
-- remove-appart-stable eq {x} (snoc# {.x} {y} {L} x#L x₁) | yes p = sym p ↯ x₁
-- remove-appart-stable eq {x} (snoc# {.x} {y} {L} x#L x₁) | no ¬p =
--   cong₂ _∷_ refl (remove-appart-stable eq x#L)

-- remove-is-#-convervative : ∀ {C} (eq : DecEq C) x y L → y # L → y # remove eq x L
-- remove-is-#-convervative eq x y .[] []# = []#
-- remove-is-#-convervative eq x y .(_ ∷ _) (snoc# {_} {y'} y#L x₁) with eq x y'
-- remove-is-#-convervative eq x y₁ .(x ∷ _) (snoc# {.y₁} {.x} y#L x₁) | yes refl = remove-is-#-convervative eq x y₁ _ y#L
-- remove-is-#-convervative eq x y₁ .(y ∷ _) (snoc# {.y₁} {y} y#L x₁) | no ¬p = snoc# (remove-is-#-convervative eq x y₁ _ y#L ) x₁

-- remove-nodup-stable : ∀ {C} (eq : DecEq C) x {M} → NoDup M → NoDup (remove eq x M)
-- remove-nodup-stable eq x [] = []
-- remove-nodup-stable eq x (_∷_ {y} y#L ndM) with eq x y
-- remove-nodup-stable eq x (y#L ∷ ndM) | yes refl =
--   let nodup-remove = remove-nodup-stable eq x ndM
--       L≡removexL = remove-appart-stable eq y#L
--   in subst (λ r → NoDup r) L≡removexL ndM
-- remove-nodup-stable eq x₁ (_∷_ {x} {L} x#L ndM) | no ¬p =
--   let ndx∷M = remove-nodup-stable eq x₁ ndM
--       x#removeyL = remove-is-#-convervative eq x₁ x L x#L
--   in x#removeyL ∷ ndx∷M

-- add-remove-nodup-stable : ∀ {C} (eq : DecEq C) x {M} →
--   NoDup M → NoDup (x ∷ (remove eq x M))
-- add-remove-nodup-stable eq x {M} ndM =
--   remove⇒appart eq x M ∷ remove-nodup-stable eq x ndM

-- remove-choice : ∀ {C} (eq : DecEq C) x y M → y ∈ M → y ∈ remove eq x M ⊎ x ≡ y
-- remove-choice eq x y M y∈M with eq x y
-- remove-choice eq x y M y∈M | yes p = inj₂ p
-- remove-choice eq x y M y∈M | no ¬p = inj₁ (remove-is-convervative eq x y M ¬p y∈M)

-- y∈removeM⇒y∈M : ∀ {C} (eq : DecEq C) x M → remove eq x M ⊆ M
-- y∈removeM⇒y∈M eq x [] y y∈remove = y∈remove
-- y∈removeM⇒y∈M eq x (x₁ ∷ M) y y∈remove with eq x x₁
-- y∈removeM⇒y∈M eq x (x₁ ∷ M) y y∈remove | yes p = there (y∈removeM⇒y∈M eq x M y y∈remove)
-- y∈removeM⇒y∈M eq x (x₁ ∷ M) .x₁ here | no ¬p = here
-- y∈removeM⇒y∈M eq x (x₁ ∷ M) x₂ (there y∈remove) | no ¬p = there (y∈removeM⇒y∈M eq x M x₂ y∈remove)

-- _∪_ : ∀ {C : Set} → List C → List C → List C
-- S ∪ T = S ++ T

-- InUnionLeft : ∀ {C : Set} {S : List C} S₁ {a} → a ∈ S → a ∈ (S ∪ S₁)
-- InUnionLeft {_} {[]} S₁ ()
-- InUnionLeft {_} {(a ∷ S)} S₁ here = here
-- InUnionLeft {_} {(x ∷ S)} S₁ (there p) = there $ InUnionLeft S₁ p

-- InUnionRight : ∀ {C : Set} (S : List C) {S₁ a} → a ∈ S₁ → a ∈ (S ∪ S₁)
-- InUnionRight [] here = here
-- InUnionRight [] (there p) = there $ InUnionRight [] p
-- InUnionRight (x ∷ S) p = there $ InUnionRight S p

-- NotInUnionLeft : ∀ {C : Set} {S : List C} S₁ {a} → a ∉ (S ∪ S₁) → a ∉ S
-- NotInUnionLeft {C} {S} S₁ p q = p $ InUnionLeft {C} {S} S₁ q

-- NotInUnionRight : ∀ {C} S {S₁ : List C} {a} → a ∉ (S ∪ S₁) → a ∉ S₁
-- NotInUnionRight S {S₁} p q = p $ InUnionRight S {S₁} q

-- S⊆T⇒x∷S⊆x∷T : ∀ {X : Set} (S T : List X) x → S ⊆ T → (x ∷ S) ⊆ (x ∷ T)
-- S⊆T⇒x∷S⊆x∷T S T x S⊆T .x here = here
-- S⊆T⇒x∷S⊆x∷T S T x S⊆T x₁ (there y∈x∷S) = there (S⊆T x₁ y∈x∷S)

-- x∷S⊆x∷T⇒S⊆T : ∀ {X : Set} {S T : List X} {x} →
--   NoDup (x ∷ S) → NoDup (x ∷ T) → (x ∷ S) ⊆ (x ∷ T) → S ⊆ T
-- x∷S⊆x∷T⇒S⊆T (y#S ∷ ndS) ndT x∷S⊆x∷T y y∈S with x∷S⊆x∷T y (there y∈S)
-- x∷S⊆x∷T⇒S⊆T (y#S ∷ ndS) (x₂ ∷ ndT) x∷S⊆x∷T y y∈S | here = ⊥-elim (∈∧#⇒⊥ y#S y∈S)
-- x∷S⊆x∷T⇒S⊆T (y#S ∷ ndS) (x₂ ∷ ndT) x∷S⊆x∷T y y∈S | there res = res

-- x∈S∪T⇒x∈S⊎x∈T : ∀ {X : Set} (S T : List X) x →
--   x ∈ (S ∪ T) → x ∈ S ⊎ x ∈ T
-- x∈S∪T⇒x∈S⊎x∈T [] T x x∈S∪T = inj₂ x∈S∪T
-- x∈S∪T⇒x∈S⊎x∈T (x ∷ S) T .x here = inj₁ here
-- x∈S∪T⇒x∈S⊎x∈T (x ∷ S) T x₁ (there x∈S∪T) with x∈S∪T⇒x∈S⊎x∈T S T x₁ x∈S∪T
-- x∈S∪T⇒x∈S⊎x∈T (x₂ ∷ S) T x₁ (there x∈S∪T) | inj₁ x = inj₁ (there x)
-- x∈S∪T⇒x∈S⊎x∈T (x ∷ S) T x₁ (there x∈S∪T) | inj₂ y = inj₂ y

-- NotInUnion : ∀ {C} S₁ S₂ (a : C) → a ∉ S₁ → a ∉ S₂ → a ∉ (S₁ ∪ S₂)
-- NotInUnion S₁ S₂ a a∉S₁ a∉S₂ a∈S₁∪S₂ with x∈S∪T⇒x∈S⊎x∈T S₁ S₂ a a∈S₁∪S₂
-- NotInUnion S₁ S₂ a a∉S₁ a∉S₂ a∈S₁∪S₂ | inj₁ x = a∉S₁ x
-- NotInUnion S₁ S₂ a a∉S₁ a∉S₂ a∈S₁∪S₂ | inj₂ y = a∉S₂ y

-- A∪B⊆A∪x∷B : ∀ {X : Set} (A B : List X) x →
--   (A ∪ B) ⊆ (A ∪ (x ∷ B))
-- A∪B⊆A∪x∷B A B x y y∈A∪B with x∈S∪T⇒x∈S⊎x∈T A B y y∈A∪B
-- A∪B⊆A∪x∷B A B x₁ y y∈A∪B | inj₁ p = InUnionLeft (x₁ ∷ B) p
-- A∪B⊆A∪x∷B A B x y y∈A∪B | inj₂ p = InUnionRight A (there p)

-- -- A generalisation of the above
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T : ∀ {X : Set} (A B S T : List X) x →
--   (A ∪ B) ⊆ (S ∪ T) → (A ∪ (x ∷ B)) ⊆ (S ∪ (x ∷ T))
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B
--   with x∈S∪T⇒x∈S⊎x∈T A (x ∷ B) y y∈A∪x∷B
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B
--   | inj₁ x₁ with A∪B⊆S∪T y (InUnionLeft B x₁)
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B | inj₁ x₁ | y∈S∪T
--                     with x∈S∪T⇒x∈S⊎x∈T S (x ∷ T) y (A∪B⊆A∪x∷B S T x y y∈S∪T)
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B
--   | inj₁ x₂ | y∈S∪T | inj₁ x₁ = InUnionLeft (x ∷ T) x₁
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B
--   | inj₁ x₁ | y∈S∪T | inj₂ y₁ = InUnionRight S y₁
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T y A∪B⊆S∪T .y y∈A∪x∷B | inj₂ here = InUnionRight S here
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B | inj₂ (there y₁) with A∪B⊆S∪T y (InUnionRight A y₁)
-- A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B S T x A∪B⊆S∪T y y∈A∪x∷B | inj₂ (there y₁) | u∈S∪T = A∪B⊆A∪x∷B S T x y u∈S∪T

-- A⊆B⇒C⊆D⇒A∪C⊆B∪D : ∀ {X : Set} {A B C D : List X} → A ⊆ B → C ⊆ D → (A ∪ C) ⊆ (B ∪ D)
-- A⊆B⇒C⊆D⇒A∪C⊆B∪D {A = A} {C = C} A⊆B C⊆D x x∈A∪C with x∈S∪T⇒x∈S⊎x∈T A C _ x∈A∪C
-- A⊆B⇒C⊆D⇒A∪C⊆B∪D {D = D} A⊆B C⊆D x x∈A∪C | inj₁ x₁ = InUnionLeft D (A⊆B x x₁)
-- A⊆B⇒C⊆D⇒A∪C⊆B∪D {B = B} A⊆B C⊆D x x∈A∪C | inj₂ y = InUnionRight B (C⊆D x y)

-- vennise : ∀ {X : Set} → (eq : DecEq X) → List X → List X → List X × List X × List X
-- vennise eq [] M = [] , [] , M
-- vennise eq (x ∷ L) M with eq2in eq x M
-- vennise eq (x ∷ L) M | yes p with vennise eq L (remove eq x M)
-- vennise eq (x ∷ L) M | yes p | A , B , C = A , x ∷ B , C
-- vennise eq (x ∷ L) M | no ¬p with vennise eq L M
-- vennise eq (x ∷ L) M | no ¬p | A , B , C = x ∷ A , B , C

-- left : ∀ {ℓ} {A : Set ℓ} → A × A × A → A
-- left = proj₁

-- middle : ∀ {ℓ} {A : Set ℓ} → A × A × A → A
-- middle = proj₁ ∘ proj₂

-- right : ∀ {ℓ} {A : Set ℓ} → A × A × A → A
-- right = proj₂ ∘ proj₂

-- vennise-sub-left : ∀ {X : Set} → (eq : DecEq X) → ∀ (N M : List X) → ((left (vennise eq N M)) ∪ (middle (vennise eq N M))) ≈ N
-- vennise-sub-left eq [] M = (λ x x₁ → x₁) , (λ x x₁ → x₁)
-- vennise-sub-left eq (x ∷ N) M with eq2in eq x M
-- vennise-sub-left eq (x ∷ N) M | yes p with vennise eq N (remove eq x M) | vennise-sub-left eq N (remove eq x M)
-- vennise-sub-left eq (x ∷ N) M | yes p | A , B , C | A∪B⊆N , N⊆A∪B =
--   (λ a a∈A∪x∷B → A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T A B [] N x A∪B⊆N a a∈A∪x∷B) , (λ a x∈a∷N → hereOrThere a x A B N x∈a∷N N⊆A∪B)
--   where hereOrThere : ∀ {X : Set} (a x : X) A B N → a ∈ (x ∷ N) → N ⊆ (A ∪ B) → a ∈ (A ∪ (x ∷ B))
--         hereOrThere a .a A₁ B₁ N here N⊆A∪B = InUnionRight A₁ here
--         hereOrThere a x A₁ B₁ N (there a∈x∷N) N⊆A∪B = let res = N⊆A∪B a a∈x∷N in A∪B⊆A∪x∷B A₁ B₁ x a (N⊆A∪B a a∈x∷N)
-- vennise-sub-left eq (x ∷ N) M | no ¬p with vennise eq N M | vennise-sub-left eq N M
-- vennise-sub-left eq (x ∷ N) M | no ¬p | A , B , C | A∪B⊆N , N⊆A∪B = (S⊆T⇒x∷S⊆x∷T (A ++ B) N x A∪B⊆N , S⊆T⇒x∷S⊆x∷T N (A ++ B) x N⊆A∪B)

-- --- Useful due to where clauses being fussy
-- here⊎there : ∀ {X : Set} (a : X) x B → a ∈ (x ∷ B) → a ≡ x ⊎ a ∈ B
-- here⊎there a .a B here = inj₁ refl
-- here⊎there a x B (there a∈x∷B) = inj₂ a∈x∷B

-- vennise-sub-right : ∀ {X : Set} → (eq : DecEq X) → ∀ (N M : List X) → ((middle (vennise eq N M)) ∪ (right (vennise eq N M))) ≈ M
-- vennise-sub-right eq [] M = (λ x x₁ → x₁) , (λ x x₁ → x₁)
-- vennise-sub-right eq (x ∷ N) M with eq2in eq x M
-- vennise-sub-right eq (x ∷ N) M | yes p with vennise eq N (remove eq x M) | vennise-sub-right eq N (remove eq x M)
-- vennise-sub-right eq (x ∷ N) M | yes p | A , B , C | A∪B⊆N , N⊆A∪B = leftSide , rightSide
--   where rightSide : ∀ a → a ∈ M → a ∈ ((x ∷ B) ∪ C)
--         rightSide a a∈M with remove-choice eq x a M a∈M
--         rightSide a a∈M | inj₁ p = let res = N⊆A∪B a p in InUnionRight [] (there (N⊆A∪B a p))
--         rightSide a a∈M | inj₂ p rewrite p = here
--         leftSide : ∀ a → a ∈ (x ∷ B ∪ C) → a ∈ M
--         leftSide a a∈x∷B∪C with here⊎there a x (B ∪ C) a∈x∷B∪C
--         leftSide a a∈x∷B∪C | inj₁ q rewrite q = p
--         leftSide a a∈x∷B∪C | inj₂ q = let res = A∪B⊆N a q in y∈removeM⇒y∈M eq x M a res
-- vennise-sub-right eq (x ∷ N) M | no ¬p with vennise eq N M | vennise-sub-right eq N M
-- vennise-sub-right eq (x ∷ N) M | no ¬p | A , B , C | A∪B⊆N , N⊆A∪B = A∪B⊆N , N⊆A∪B

-- vennise-middle-left : ∀ {X : Set} → (eq : DecEq X) → ∀ (N M : List X) → (middle (vennise eq N M)) ⊆ N
-- vennise-middle-left eq [] M = λ x z → z
-- vennise-middle-left eq (x ∷ N) M with eq2in eq x M
-- vennise-middle-left eq (x ∷ N) M | yes p with vennise eq N (remove eq x M) | vennise-middle-left eq N (remove eq x M)
-- vennise-middle-left eq (x ∷ N) M | yes p | A , B , C | sub = A∪B⊆S∪T⇒A∪x∷B⊆S∪x∷T [] B [] N x sub
-- vennise-middle-left eq (x ∷ N) M | no ¬p with vennise eq N (remove eq x M) | vennise-middle-left eq N M
-- vennise-middle-left eq (x ∷ N) M | no ¬p | A , B , C | sub = λ α α∈NM → there (sub α α∈NM)

-- vennise-middle-right : ∀ {X : Set} → (eq : DecEq X) → ∀ (N M : List X) → (middle (vennise eq N M)) ⊆ M
-- vennise-middle-right eq [] M = λ x → λ ()
-- vennise-middle-right eq (x ∷ N) M with eq2in eq x M
-- vennise-middle-right eq (x ∷ N) M | yes p with vennise eq N (remove eq x M) | vennise-middle-right eq N (remove eq x M)
-- vennise-middle-right eq (x ∷ N) M | yes p | A , B , C | sub = α∈M
--   where α∈M : ∀ α → α ∈ (x ∷ B) → α ∈ M
--         α∈M α α∈x∷B with here⊎there α x B α∈x∷B
--         α∈M α α∈x∷B | inj₁ q rewrite q = p
--         α∈M α α∈x∷B | inj₂ q = y∈removeM⇒y∈M eq x M α (sub α q)
-- vennise-middle-right eq (x ∷ N) M | no ¬p with vennise eq N (remove eq x M) | vennise-middle-right eq N M
-- vennise-middle-right eq (x ∷ N) M | no ¬p | A , B , C | sub = sub

-- _≺⟨_⟩_ : {C : Set} → List C → (eq : DecEq C) → List C → Set
-- S ≺⟨ eq ⟩ T = ∣ S ∣⟨ eq ⟩ <′ ∣ T ∣⟨ eq ⟩

-- _⊂⟨_⟩_ : {C : Set} → List C → (eq : DecEq C) → List C → Set
-- S ⊂⟨ eq ⟩ T = S ⊆ T × S ≺⟨ eq ⟩ T

-- {-
-- _<?_ : ∀ n m → Dec (n <′ m)
-- zero <? zero = no (λ ())
-- zero <? suc m = yes (aux m)
--   where aux : ∀ m → zero <′ suc m
--         aux zero = ≤′-refl
--         aux (suc m₁) = ≤′-step (aux m₁)
-- suc n <? zero = no (λ ())
-- suc n <? suc m with n <? m
-- suc n <? suc m | yes p = yes (n≤m⇒1+n≤1+m _ _ p)
-- suc n <? suc m | no ¬p = no (λ x → ¬p (1+n≤1+m⇒n≤m (suc n) m x))
-- -}
-- _⊂⟨_⟩?_ : {C : Set} → (S : List C) → (eq : DecEq C) → (T : List C) → Dec (S ⊂⟨ eq ⟩ T)
-- S ⊂⟨ eq ⟩? T with S ⊆⟨ eq ⟩? T | ∣ S ∣⟨ eq ⟩ <? ∣ T ∣⟨ eq ⟩
-- S ⊂⟨ eq ⟩? T | yes p | yes p₁ = yes (p , {!!})
-- S ⊂⟨ eq ⟩? T | yes p | no ¬p = no {!¬p!} -- (¬p ∘ proj₂)
-- S ⊂⟨ eq ⟩? T | no ¬p | res₂ = no {!!} -- (¬p ∘ proj₁)
