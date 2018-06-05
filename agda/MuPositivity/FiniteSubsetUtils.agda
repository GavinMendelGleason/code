open import Utils

module FiniteSubsetUtils
  (X : Set)
  (eq : DecEq X)
  where

open import FiniteSubset
--open import Utilities.ListProperties -- renaming (_∈_ to _∈L_)
open import Data.List
open import Data.Bool
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding (inspect)
open import Data.Nat
open import Finiteness renaming (∣_∣ to ∣_∣listable)
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)
open import Function

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


∈? : ∀ {C : Set} → (eq : DecEq C) → ∀ x S → Dec (x ∈ S)
∈? eq x S = eq2in eq x S

_⊆_ : ∀ {C : Set} (T S : List C) → Set
T ⊆ S = (∀ x → x ∈ T → x ∈ S)

data ∣_∣=_ {C : Set} : List C → ℕ → Set where
  ∣[]∣ : ∣ [] ∣= 0
  ∣x∷L∣ : ∀ {x L n} → ∣ L ∣= n → x # L → ∣ x ∷ L ∣= suc n 

convert : ∀ {C} → (eq : DecEq C) → List C → Σ[ xs ∈ List C ] Σ[ n ∈ ℕ ] ∣ xs ∣= n
convert eq [] = [] , zero , ∣[]∣
convert eq (x ∷ l) with convert eq l
convert eq (x ∷ l) | xs , n , P with #? eq x xs
convert eq (x ∷ l) | xs , n , P | yes p = x ∷ xs , suc n , ∣x∷L∣ P p
convert eq (x ∷ l) | xs , n , P | no ¬p = xs , n , P

convert-sound : ∀ {C} → (eq : DecEq C) → ∀ xs y → y ∈ proj₁ (convert eq xs) → y ∈ xs
convert-sound eq [] y p = p
convert-sound eq (x ∷ xs) y p with ∈? eq y $ proj₁ (convert eq xs) 
convert-sound eq (x ∷ xs) y p₁ | yes p with convert-sound eq xs y p
convert-sound eq (x ∷ xs) y p₁ | yes p | res = there res
convert-sound eq (x ∷ xs) y p | no ¬p with #? eq x (proj₁ (convert eq xs))
convert-sound eq (x ∷ xs) y p₁ | no ¬p | yes p with #-lemma eq x y (proj₁ (convert eq xs)) ¬p p₁ p
convert-sound eq (x ∷ xs) .x p₁ | no ¬p | yes p | refl = here
convert-sound eq (x ∷ xs) y p | no ¬p₁ | no ¬p = p ↯ ¬p₁ 

convert-complete : ∀ {C} → (eq : DecEq C) → ∀ xs y → y ∈ xs → y ∈ proj₁ (convert eq xs)
convert-complete eq [] y ()
convert-complete eq (x ∷ xs) y p with ∈? eq y $ proj₁ (convert eq xs) | #? eq x (proj₁ (convert eq xs))
convert-complete eq (x ∷ xs) y p₂ | yes p | yes p₁ = there p
convert-complete eq (x ∷ xs) y p₁ | yes p | no ¬p = p
convert-complete eq (y ∷ xs) .y here | no ¬p | yes p = here
convert-complete eq (x ∷ xs) y (there p₁) | no ¬p | yes p = there (convert-complete eq xs y p₁)
convert-complete eq (y ∷ xs) .y here | no ¬p | no ¬p₁ = ¬#⇒∈ eq (proj₁ (convert eq xs)) y ¬p₁
convert-complete eq (x ∷ xs) y (there p) | no ¬p | no ¬p₁ = convert-complete eq xs y p




-- _∈_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Set
-- _∈_ {eq = eq} x S = x ∈L (listOf S)

-- _∉_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Set
-- _∉_ {eq = eq} x S = x ∈ (listOf S) → ⊥ 

--∈L? : ∀ {C : Set} (eq : DecEq C) → (x : C) → (S : List C) → Dec (x ∈ S)
--∈L? eq x S = eq2in eq x S

-- _∈𝔹_ : ∀ {C : Set}{eq : DecEq C} {b : Bool} → C → FiniteSubSet C eq b → Bool
-- _∈𝔹_ {eq = eq} x S = ⌊ eq2in eq x (listOf S ) ⌋

-- _/_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool}
--   → FiniteSubSet C eq b1 → FiniteSubSet C eq b2
--   → FiniteSubSet C eq b1
-- _/_ {C} {eq = _==_} {b1} {b2} S T = 
--         for s ∈ S as _
--         do if not (s ∈𝔹 T)
--            then return {b = true} s


_⊆L_ : ∀ {C : Set} → List C → List C → Set
_⊆L_ S T = ∀ s → s ∈ S → s ∈ T 

⊆Lx∷S⇒⊆LS : ∀ {C} {x : C} {S T} → ((x ∷ S) ⊆L T) → x ∈ T → S ⊆L T
⊆Lx∷S⇒⊆LS S⊆T x∈LT s x = S⊆T s (there x)

_⊆L?_ : ∀ {C : Set} {eq : DecEq C} → 
       Decidable (_⊆L_ {C})
[] ⊆L? T = yes (λ s → λ ())
_⊆L?_ {eq = eq} (x ∷ S) T with eq2in eq x T
_⊆L?_ {eq = eq} (x ∷ S) T | yes p with _⊆L?_ {eq = eq} S T
(x ∷ S) ⊆L? T | yes p₁ | yes p = yes (λ s x₁ → aux p₁ x₁ p)
  where aux : ∀ {C : Set} {s x : C} {T S} → x ∈ T → s ∈ (x ∷ S) → S ⊆L T → s ∈ T
        aux P here S⊆T = P
        aux P (there Q) S⊆T = S⊆T _ Q
(x ∷ S) ⊆L? T | yes p | no ¬p = no (λ x₁ → ¬p (⊆Lx∷S⇒⊆LS x₁ p))
(x ∷ S) ⊆L? T | no ¬p = no (λ z → ¬p (z x here))


{-
_⊂_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
S ⊂ T = S ⊆ T × ¬ T ⊆ S 
-}

_⊂L_ : ∀ {C : Set} →
        List C → List C → Set
S ⊂L T = S ⊆L T × ¬ T ⊆L S 

_⊂L?_ : ∀ {C : Set}{eq : DecEq C} →
       Decidable (_⊂L_ {C})
_⊂L?_ {eq = eq} S T with _⊆L?_ {eq = eq} S T

_⊂L?_ {eq = eq} S T | yes p with _⊆L?_ {eq = eq} T S
S ⊂L? T | yes p₁ | yes p = no (λ z → proj₂ z p)
S ⊂L? T | yes p | no ¬p = yes (p , ¬p)
S ⊂L? T | no ¬p = no (λ z → ¬p (proj₁ z))

-- _Σ⊂_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
--         FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
-- _Σ⊂_ {C} S T =  S ⊆ T × Σ[ x ∈ C ] x ∈ T × x ∉ S

_Σ⊂_ : ∀ {C : Set} →
        List C → List C → Set
_Σ⊂_ {C} S T = S ⊆L T × Σ[ x ∈ C ] x ∈ T × {!!} -- x ∉ S

{-
Σ⊂⇒⊂ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
     (S : FiniteSubSet C eq b1) → (T : FiniteSubSet C eq b2) →
     (S Σ⊂ T) → S ⊂ T
Σ⊂⇒⊂ S T (proj₁ , proj₂ , proj₃ , proj₄) = proj₁ , (λ x → proj₄ (x proj₂ proj₃))
-}

--open import Utilities.ListsAddition -- Utilities.ListAddition

{-
strongRemDup : ∀ {X : Set} → (∈? : DecIn X) → (xs : List X) →
               Σ[ ys ∈ List X ] xs ⊆ ys ×
                                ys ⊆ xs × 
                                NoDup ys
strongRemDup ∈? xs = (remDup ∈? xs)
                     , (λ x P → remDupSound ∈? x xs P)
                     , (λ x P → remDupComplete ∈? x xs P)
                     , (λ x → remDupCorrect ∈? xs x)

∣_∣ND : ∀  {X : Set} → ListableNoDup X → ℕ
∣_∣ND nodup = length ∘ proj₁ $ nodup

_∈ND_ : ∀ {C : Set} → C → ListableNoDup C → Set
x ∈ND T = x ∈ (proj₁ T)  -- 

_⊆ND_ : ∀ {C : Set} → (S : ListableNoDup C) → (T : ListableNoDup C) → Set
S ⊆ND T = ∀ x → x ∈ND S → x ∈ND T

_⊂ND_ : ∀ {C : Set} → (S : ListableNoDup C) → (T : ListableNoDup C) → Set
S ⊂ND T = S ⊆ND T × ¬ (T ⊆ND S) 
-}

{-
aux : ∀ {C : Set} (x s : C) (xs ys : List C) → (x ∷ xs) ⊆L (x ∷ ys) → s ∈L xs → s ∈L ys
aux x s xs ys x∷xs⊆Lx∷ys s∈Lxs s≢x with x∷xs⊆Lx∷ys s (there s∈Lxs)        
aux s .s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | here = ⊥-elim (s≢x refl)
aux x s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | there res = res
-}

-- ∀ {C : Set} (eq : DecEq C) (x : C) (xs ys : List C) → x ∷ xs ⊆L 

notInAndOut : ∀ {C : Set} (x s : C) xs → x ∉ xs → s ∈ xs → s ≢ x
notInAndOut s .s _ x∉ here refl = ⊥-elim (x∉ here) 
notInAndOut s .s _ x∉ (there s∈) refl = ⊥-elim (x∉ (there s∈))

strengthen : ∀ {C : Set} (x : C) (xs ys : List C) → x ∉ xs → (x ∷ xs) ⊆ (x ∷ ys) → (xs ⊆ ys)
strengthen x xs ys P Q y y∈ys with Q y (there y∈ys)
strengthen y xs ys P Q .y y∈ys | here = ⊥-elim $ P y∈ys 
strengthen x xs ys P Q y y∈ys | there res = res

weaken¬⊆ : ∀ {C : Set} (x : C) (xs ys : List C) → x ∉ xs → ¬ (xs ⊆L ys) → ¬ (x ∷ xs) ⊆L (x ∷ ys)
weaken¬⊆ x xs ys x∉xs ¬xs⊆ys x∷⊆Lx∷xs = ¬xs⊆ys (λ s x₁ → aux x s xs ys x∷⊆Lx∷xs x₁ (notInAndOut x s xs x∉xs x₁))
  where aux : ∀ {C : Set} (x s : C) (xs ys : List C) → (x ∷ xs) ⊆L (x ∷ ys) → s ∈ xs → s ≢ x → s ∈ ys
        aux x s xs ys x∷xs⊆Lx∷ys s∈Lxs s≢x with x∷xs⊆Lx∷ys s (there s∈Lxs)        
        aux s .s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | here = ⊥-elim (s≢x refl) -- (s≢x refl)
        aux x s xs₁ ys x∷xs⊆Lx∷ys s∈Lxs s≢x | there res = res


inMustBeHere : ∀ {C : Set} {x x₁} {S : List C} → x ∉ S → x ∈ (x₁ ∷ S) → x ≡ x₁
inMustBeHere P here = refl
inMustBeHere P (there Q) = Q ↯ P

open import Data.Sum renaming ([_,_] to ⟨_,_⟩)

_─_⟨_⟩ : ∀ {C : Set} → (S : List C) → (T : List C) → (eq : DecEq C) → Σ[ ys ∈ List C ] ∀ x → (x ∈ S × x ∈ ys × x ∉ T) ⊎ (x ∈ T → x ∉ ys)
[] ─ [] ⟨ eq ⟩ = [] , (λ x → inj₂ (λ x₁ → λ ()))
[] ─ (x ∷ T) ⟨ eq ⟩ = [] , (λ x₁ → inj₂ (λ x₂ → λ ()))
(x ∷ S) ─ T ⟨ eq ⟩ with  S ─ T ⟨ eq ⟩ 
(x ∷ S) ─ T ⟨ eq ⟩ | S' , P with eq2in eq x T
(x ∷ S) ─ T ⟨ eq ⟩ | S' , P | yes p = S' , (λ x₁ → aux x₁ (P x₁))
  where aux : ∀ {C : Set} {x S S' T} → (x₁ : C) → (x₁ ∈ S) × (x₁ ∈ S') × (x₁ ∉ T) ⊎ (x₁ ∈ T → x₁ ∉ S') →
                                                   (x₁ ∈ (x ∷ S)) × (x₁ ∈ S') × (x₁ ∉ T) ⊎ (x₁ ∈ T → x₁ ∉ S')
        aux x₂ (inj₁ x₃) = inj₁ (there (proj₁ x₃) , ((proj₁ (proj₂ x₃)) , (proj₂ (proj₂ x₃))))
        aux x₂ (inj₂ y) = inj₂ y 
(x ∷ S) ─ T ⟨ eq ⟩ | S' , P | no ¬p = x ∷ S' , (λ x₁ → aux x₁ ¬p (P x₁))
  where aux : ∀ {C : Set} {x S S' T} → (x₁ : C) → x ∉ T → (x₁ ∈ S) × (x₁ ∈ S') × (x₁ ∉ T) ⊎ (x₁ ∈ T → x₁ ∉ S') → 
                                                            (x₁ ∈ (x ∷ S)) × (x₁ ∈ (x ∷ S')) × (x₁ ∉ T) ⊎ (x₁ ∈ T → x₁ ∉ (x ∷ S')) 
        aux x₂ P₁ (inj₁ x₃) = inj₁ ((there (proj₁ x₃)) , ((there (proj₁ (proj₂ x₃))) , (proj₂ (proj₂ x₃))))
        aux x₂ P₁ (inj₂ y) = inj₂ (λ x₁ x₃ → let p = y x₁ ;
                                                  q = inMustBeHere p x₃
                                              in P₁ (subst (λ z → z ∈ _) q x₁)) 
--  S ⊂L T → NoDupInd S → S ⊂ T
--open import Data.Sum

--drop : ∀ {A : Set} (x : A) → List A → List A
--drop x S = ? 

_̸_ : List X → List X → List X
S ̸ T = foldr (λ x r → (filter (λ y → ⌊ eq x y ⌋) r)) S T


{- Strict subset based on cardinality - easier to do well founded induction with -}
_⊂ᶜ_[_] : ∀ {C} → List C → List C → (DecEq C) → Set
S ⊂ᶜ T [ eq ] = S ⊆L T × Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] (∣ S ∣= n) × (∣ T ∣= m) × n <′ m 

_⊂_ : ∀ {C : Set}{eq : DecEq C}{b1 b2 : Bool} →
        FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
_⊂_ {eq = eq} F G = proj₁ (convert eq (listOf F)) ⊂ᶜ proj₁ (convert eq (listOf G)) [ eq ]

n≤m⇒1+n≤1+m : ∀ n m → n ≤′ m → suc n ≤′ suc m
n≤m⇒1+n≤1+m n .n ≤′-refl = ≤′-refl
n≤m⇒1+n≤1+m n₁ _ (≤′-step p) with n≤m⇒1+n≤1+m n₁ _ p
n≤m⇒1+n≤1+m n₁ _ (≤′-step p) | res = ≤′-step res 

1+n≤1+m⇒n≤m : ∀ n m → suc n ≤′ suc m → n ≤′ m 
1+n≤1+m⇒n≤m n .n ≤′-refl = ≤′-refl
1+n≤1+m⇒n≤m n zero (≤′-step ())
1+n≤1+m⇒n≤m n (suc m) (≤′-step p) = ≤′-step (1+n≤1+m⇒n≤m n m p) 

_<?_ : ∀ n m → Dec (n <′ m)
zero <? zero = no (λ ())
zero <? suc m = yes (aux m)
  where aux : ∀ m → zero <′ suc m
        aux zero = ≤′-refl
        aux (suc m₁) = ≤′-step (aux m₁)
suc n <? zero = no (aux n)
  where aux : ∀ n → suc n <′ zero → ⊥
        aux n₁ ()
suc n <? suc m with n <? m
suc n <? suc m | yes p = yes (n≤m⇒1+n≤1+m _ _ p)
suc n <? suc m | no ¬p = no (λ x → ¬p (1+n≤1+m⇒n≤m (suc n) m x))

_⊂?_ : ∀ {C} {eq : DecEq C} {b1 b2} → (F : FiniteSubSet C eq b1) → (G : FiniteSubSet C eq b2) → Dec (F ⊂ G)
_⊂?_ {eq = eq} F G with _⊆L?_ {eq = eq} (listOf F) (listOf G)
_⊂?_ {eq = eq} F G | yes p with convert-sound eq (listOf F) | convert-sound eq (listOf G)
_⊂?_ {eq = eq} F G | yes p | Q | R with convert eq (listOf F) | convert eq (listOf G)
F ⊂? G | yes p₁ | Q | R | L , n , S | L' , m , S' with n <? m
F ⊂? G | yes p₁ | Q | R | L , n , S | L' , m , S' | yes p = yes ({!!} , ({!!} , ({!!} , ({!!} , ({!!} , {!!})))))
F ⊂? G | yes p₁ | Q | R | L , n , S | L' , m , S' | no ¬p = {!!}
F ⊂? G | no ¬p = no {!!}

open import Induction.WellFounded

--<-well-founded

{-
ℕ-wf : Well-founded _<′_
ℕ-wf n = acc (aux n)
  where aux : ∀ x y → y <′ x → Acc _<′_ y
        aux .(suc y) y ≤′-refl = ℕ-wf y
        aux .(suc x) y (≤′-step {x} p) = aux x y p 
-}

{-
open import Function

∣_∣ : ∀ {C : Set} {eq : DecEq C} {b1 : Bool} →
      FiniteSubSet C eq b1 → ℕ
∣ S ∣ = length ∘ proj₁ $ lstbl2nodup (fsListable S)

open import Data.Nat

_≺_ : {C : Set}{eq : DecEq C} {b1 b2 : Bool} →
      FiniteSubSet C eq b1 → FiniteSubSet C eq b2 → Set
S ≺ T = ∣ S ∣ <′ ∣ T ∣  

open import Induction.WellFounded
open import Induction.Nat

module WF⊆mod (C : Set) (eq : DecEq C) (b : Bool) where
  open Inverse-image {_<_ = _<′_} (∣_∣ {C} {eq} {b}) renaming (well-founded to well-founded-ii-obj)
  {- The inverse image of a well founded relation is well founded. -}

  wf≺ : Well-founded _≺_
  wf≺ = well-founded-ii-obj <-well-founded

  ⊂⇒<′ : ∀ {S T : FiniteSubSet C eq b} → S ⊂ T → S ≺ T
  ⊂⇒<′ {S} {T} P with S ⊆? T
  ⊂⇒<′ {S} {T} P | yes p with T ⊆? S
  ⊂⇒<′ (proj₁ , proj₂) | yes p₁ | yes p = ⊥-elim (proj₂ p)
  ⊂⇒<′ (proj₁ , proj₂) | yes p | no ¬p = {!!}
  ⊂⇒<′ (proj₁ , proj₂) | no ¬p = ⊥-elim (¬p proj₁)

{-
open Subrelation {A = Database} {_<₁_ = (_⊂_)} {_<₂_ =  _≺_} ⊂⇒<′
  renaming (well-founded to well-founded-subrelation)

{- The sub relation of a well-founded relation is well founded -}
wf⊂ : Well-founded _⊂_ 
wf⊂ = well-founded-subrelation wf≺

-}

{-
open Inverse-image {_<_ = _<′_} (∣_∣ {true} {DataTriple} {eqDataTriple}) renaming (well-founded to well-founded-ii-dat)
{- The inverse image of a well founded relation is well founded. -}
wf≺dat : Well-founded _≺dat_
wf≺dat = well-founded-ii-dat <-well-founded
-}

-}
