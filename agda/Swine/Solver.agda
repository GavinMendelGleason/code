open import Utils
open import Data.Product hiding (map) renaming (_×_ to _∧_)
open import Relation.Binary.PropositionalEquality 
open import Data.List renaming (map to mapl)
open import Data.Empty

module Solver (A : Set) where

open import Data.Sum renaming (_⊎_ to _∨_ ; [_,_] to ⟪_,_⟫)
open import Relation.Nullary
open import Relation.Nullary.Negation using () renaming (contradiction to _↯_)

open import Data.Unit hiding (_≤?_ ; _≤_ ; _≟_)
open import Data.Empty
open import Data.Product
open import Data.Bool hiding (_≟_) renaming (_∧_ to _&&_ ; _∨_ to _∥_)


{- This would be a very interesting experiment had I the time to
   explore implementing an equation solver...  perhaps another time -} 
open import Data.Nat

open import Data.Unit hiding (_≤?_ ; _≤_ ; _≟_)
open import Data.Empty
open import Data.Product
open import Data.Bool hiding (_≟_) renaming (_∧_ to _&&_ ; _∨_ to _∥_)

open import Relation.Nullary.Decidable

data L : Set where
  Eq : ℕ → ℕ → L
  Neq : ℕ → ℕ → L
  And : L → L → L
  Or : L → L → L

⟦_⟧ : L → Set
⟦ Eq x y ⟧ = x ≡ y
⟦ Neq x y ⟧ = x ≢ y 
⟦ And a b ⟧ = ⟦ a ⟧ ∧ ⟦ b ⟧
⟦ Or a b ⟧ = ⟦ a ⟧ ∨ ⟦ b ⟧ 

Goal : Set
Goal = ℕ × ℕ

Env : Set
Env = List (ℕ ∧ ℕ)

order : ℕ ∧ ℕ → ℕ ∧ ℕ
order (n , m) with n ≤? m
order (n , m) | yes p = n , m
order (n , m) | no ¬p = m , n

open import Function

inv-suc : ∀ n m → suc n ≤ suc m → n ≤ m
inv-suc n m (s≤s q) = q

n≰m⇒m≤n : ∀ n m → n ≰ m → m ≤ n
n≰m⇒m≤n zero zero p = z≤n
n≰m⇒m≤n zero (suc m) p = z≤n ↯ p
n≰m⇒m≤n (suc n) zero p = z≤n
n≰m⇒m≤n (suc n) (suc m) p = s≤s (n≰m⇒m≤n n m ((p ∘ s≤s)))

order-orders : ∀ n m r s → order ( n , m ) ≡ ( r , s ) → (r ≤ s) ∧ (r ≡ n ∧ s ≡ m ∨ r ≡ m ∧ s ≡ n)
order-orders n m r s p with n ≤? m
order-orders n m .n .m refl | yes p = p , (inj₁ (refl , refl))
order-orders n m .m .n refl | no ¬p = n≰m⇒m≤n n m ¬p , inj₂ (refl , refl)

lookup : ℕ → ℕ → Env → Bool
lookup n m [] = false
lookup n m ((r , s) ∷ xs) = ⌊ n ≟ r ⌋ && ⌊ m ≟ s ⌋ ∥ lookup n m xs

{-
Always substitute to higher indices.


-- x = y ,  z = x,  x (1) = y (2)  , z (0) = y (2) =>  x (1) = y (2)
-- x = y , m = x,  => m = y
-}

rewrite-pair : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
rewrite-pair n m r s with n ≟ r
... | yes p = m , s
... | no ¬p with n ≟ s
...         | yes p₁ = r , m
...         | no ¬p₁ = r , s

rewrite-lemma : ∀ x y z → rewrite-pair x x y z ≡ (y , z)
rewrite-lemma x y z with x ≟ z
rewrite-lemma x y .x | yes refl with x ≟ x
rewrite-lemma x y .x | yes refl | yes p = {!!}
rewrite-lemma x y .x | yes refl | no ¬p = refl ↯ ¬p 
rewrite-lemma x y z | no ¬p with x ≟ x
rewrite-lemma x y z | no ¬p | yes refl = {!!}
rewrite-lemma x y z | no ¬p₁ | no ¬p = refl ↯ ¬p

⟨_,_⟩ᵣ : ℕ → ℕ → L → L
⟨ x , y ⟩ᵣ (Eq x₁ x₂) = uncurry Eq $ rewrite-pair x y x₁ x₂
⟨ x , y ⟩ᵣ (Neq x₁ x₂) = uncurry Neq $ rewrite-pair x y x₁ x₂
⟨ x , y ⟩ᵣ (And l l₁) = And (⟨ x , y ⟩ᵣ l) (⟨ x , y ⟩ᵣ l₁)
⟨ x , y ⟩ᵣ (Or l l₁) = Or (⟨ x , y ⟩ᵣ l) (⟨ x , y ⟩ᵣ l₁)

↑ : Env → Set
↑ [] = ⊤ 
↑ ((a , b) ∷ env) = a ≡ b × ↑ env 

negContr : Env → Bool
negContr [] = false
negContr ((n , m) ∷ xs) = ⌊ n ≟ m ⌋ ∥ negContr xs

negCheck : Env → Env → Bool
negCheck [] neg = negContr neg
negCheck ((x , y) ∷ env) neg = negCheck env (mapl (uncurry $ rewrite-pair x y) neg) 

goalCheck : Env → ℕ × ℕ → Bool
goalCheck [] (x , y) = ⌊ x ≟ y ⌋ 
goalCheck ((x , y) ∷ env) G = goalCheck env (uncurry (rewrite-pair x y) G)

goalCheckCorrect : ∀ env x y → T (goalCheck env (x , y)) → ↑ env → x ≡ y
goalCheckCorrect [] x y P Q with x ≟ y
goalCheckCorrect [] x y P Q | yes p = p
goalCheckCorrect [] x y () Q | no ¬p
goalCheckCorrect (pair ∷ env) x y P Q with goalCheckCorrect env x y
goalCheckCorrect ((a , b) ∷ env) x y P Q | f with a ≟ x
goalCheckCorrect ((x , .x) ∷ env) .x y P (refl , Q) | f | yes refl = f P Q
goalCheckCorrect ((a , b) ∷ env) x y P Q | f | no ¬p with a ≟ y
goalCheckCorrect ((a , .a) ∷ env) x .a P (refl , Q) | f | no ¬p | yes refl = f P Q
goalCheckCorrect ((a , b) ∷ env) x y P Q | f | no ¬p₁ | no ¬p = f P (proj₂ Q)

{- with proj₁ x ≟ x₁
goalCheckCorrect (x ∷ env) _ y P | f | yes refl = {!!}
goalCheckCorrect (x ∷ env) x₁ y P | f | no ¬p with proj₁ x ≟ y
goalCheckCorrect (x ∷ env) x₁ _ P | f | no ¬p | yes refl = {!!}
goalCheckCorrect (x ∷ env) x₁ y P | f | no ¬p₁ | no ¬p = f P
-}

open import Data.Maybe hiding (Eq)

{- This is going to require a termination argument! -}
interp : ℕ → L → Env → Env → Goal → Env ∧ Env ∧ Bool
interp zero L env neg G = env , neg , false -- negCheck env neg ∥ goalCheck env G
interp (suc n) (Eq x y) env neg G = let ρ = ⟦ Eq x y ⟧ ∷ env in ρ , neg , negCheck ρ neg ∥ goalCheck ρ ∷ env) G
interp (suc n) (Neq x x₁) env neg G = env , (x , x₁) ∷ neg , negCheck env ((x , x₁ ) ∷  neg) ∥ goalCheck env G
interp (suc n) (And L L₁) env neg G with interp n L env neg G
interp (suc n) (And L L₁) env neg G | env₁ , neg₁ , false = interp n L₁ env₁ neg₁ G
interp (suc n) (And L L₁) env neg G | env₁ , neg₁ , true = [] , [] , true
interp (suc n) (Or L L₁) env neg G with interp n L env neg G
interp (suc n) (Or L L₁) env neg G | _ , _ , false = [] , [] , false
interp (suc n) (Or L L₁) env neg G | _ , _ , true = interp n L₁ env neg G

envCorrect : ∀ x y env neg → T (negCheck env neg ∥ goalCheck env (x , y)) → x ≡ y
envCorrect x y env neg = {!!}


interpCorrect : ∀ n L x y env neg → T (proj₂ (proj₂ (interp n L env neg (x , y)))) → ⟦ L ⟧ → x ≡ y
interpCorrect zero L x y env neg ()
interpCorrect (suc n) (Eq x .x) x₂ y env neg p refl = {!!}
interpCorrect (suc n) (Neq x x₁) x₂ y env neg p = {!!}
interpCorrect (suc n) (And L L₁) x y env neg p with interpCorrect n L x y env neg
interpCorrect (suc n) (And L L₁) x y env neg p | f with interp n L env neg (x , y)
interpCorrect (suc n) (And L L₁) x y env neg p | f | env₁ , neg₁ , false with interpCorrect n L₁ x y env₁ neg₁
interpCorrect (suc n) (And L L₁) x y env neg p | f | env₁ , neg₁ , false | g with interp n L₁ env₁ neg₁ (x , y)
interpCorrect (suc n) (And L L₁) x y env neg () | f | env₁ , neg₁ , false | g | env₂ , neg₂ , false
interpCorrect (suc n) (And L L₁) x y env neg p | f | env₁ , neg₁ , false | g | env₂ , neg₂ , true = (g tt) ∘ proj₂
interpCorrect (suc n) (And L L₁) x y env neg p | f | env₁ , neg₁ , true = (f tt) ∘ proj₁
interpCorrect (suc n) (Or L L₁) x y env neg p with interpCorrect n L x y env neg
interpCorrect (suc n) (Or L L₁) x y env neg p | f with interp n L env neg (x , y)
interpCorrect (suc n) (Or L L₁) x y env neg () | f | env₁ , neg₁ , false
interpCorrect (suc n) (Or L L₁) x y env neg p | f | env₁ , neg₁ , true with interpCorrect n L₁ x y env neg
interpCorrect (suc n) (Or L L₁) x y env neg p | f | env₁ , neg₁ , true | g with interp n L₁ env neg (x , y)
interpCorrect (suc n) (Or L L₁) x y env neg () | f | env₁ , neg₁ , true | g | env₂ , neg₂ , false
interpCorrect (suc n) (Or L L₁) x y env neg p | f | env₁ , neg₁ , true | g | env₂ , neg₂ , true = ⟪ f tt , g tt ⟫


example : L
example = (And (Eq 0 1) (And (Eq 0 2) (Neq 1 2)))

--test : proj₂ (interp 30 example nothing [] (0 , 0)) ≡ true
--test = refl 

test3 : rewrite-pair 0 1 1 2 ≡ (1 , 2)
test3 = refl

