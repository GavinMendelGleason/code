
module RDF where

{-

This module implements a rough cut of RDF.

Some complexity around (non)duplication of triples ignored (FIXME)

-} 
open import Data.String renaming (_≟_ to eqString)
open import Data.Nat renaming (_≟_ to eqNat)
open import Data.Bool renaming (_≟_ to eqBool)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; cong ; refl)

data D : Set where
  n : ℕ → D
  b : Bool → D
  s : String → D
  
data DT : Set where
  Natural : DT
  Boolean : DT
  Str : DT

data ⊢ᵟ_∶_ : D → DT → Set where
  NI : ∀ {m} → ⊢ᵟ n m ∶ Natural
  BI : ∀ {x} → ⊢ᵟ b x ∶ Boolean
  SI : ∀ {o} → ⊢ᵟ s o ∶ Str

typeDec : Decidable (⊢ᵟ_∶_)
typeDec (n x) Natural = yes NI
typeDec (n x) Boolean = no (λ ())
typeDec (n x) Str = no (λ ())
typeDec (b x) Natural = no (λ ())
typeDec (b x) Str = no (λ ())
typeDec (b x) Boolean = yes BI
typeDec (s o) Str = yes SI
typeDec (s o) Boolean = no (λ ())
typeDec (s o) Natural = no (λ ())

ninv : ∀ {x x₁} → n x ≡ n x₁ → x ≡ x₁
ninv refl = refl

binv : ∀ {x x₁} → b x ≡ b x₁ → x ≡ x₁
binv refl = refl

sinv : ∀ {x x₁} → s x ≡ s x₁ → x ≡ x₁
sinv refl = refl

eqD : Decidable {A = D} _≡_
eqD (n x) (n x₁) with eqNat x x₁
eqD (n x) (n x₁) | yes p = yes (cong n p)
eqD (n x) (n x₁) | no ¬p = no (λ neq → ¬p (ninv neq))
eqD (n x) (b x₁) = no (λ ())
eqD (b x) (n x₁) = no (λ ())
eqD (b x) (b x₁) with eqBool x x₁
eqD (b x) (b x₁) | yes p = yes (cong b p)
eqD (b x) (b x₁) | no ¬p = no (λ beq → ¬p (binv beq))
eqD (n x) (s o) = no (λ ())
eqD (b x) (s o) = no (λ ())
eqD (s o) (s p) with eqString o p
eqD (s o) (s p) | yes p₁ = yes (cong s p₁)
eqD (s o) (s p) | no ¬p = no (λ seq → ¬p (sinv seq))
eqD (s o) (n m) = no (λ ())
eqD (s o) (b x) = no (λ ())

import MuPlus
module MuMod = Mu String String D eqString eqString eqD DT ⊢ᵟ_∶_ typeDec
open MuMod public
