
module Term where 

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.List 
--open import Data.Bool 
open import Data.Product renaming (_,_ to _,ᵖ_) 
open import Relation.Binary.PropositionalEquality --using (_≡_; refl)
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary
open import Function

data ⋆ : Set where 
  ι : ⋆ 
  _⇒_ : ⋆ → ⋆ → ⋆ 

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx → ⋆ → Ctx

data _∋_ : Ctx → ⋆ → Set where
  top : ∀ {Γ τ} → (Γ , τ) ∋ τ 
  pop : ∀ {Γ τ σ} → Γ ∋ τ → (Γ , σ) ∋ τ 

data _⊢_ : Ctx → ⋆ → Set where 
  ν : ∀ {Γ τ} → Γ ∋ τ → Γ ⊢ τ 
  ƛ : ∀ {Γ τ σ} → (Γ , σ) ⊢ τ → Γ ⊢ (σ ⇒ τ)
  _·_ : ∀ {Γ τ σ} → Γ ⊢ (σ ⇒ τ) → Γ ⊢ σ → Γ ⊢ τ 

⟦_⟧⋆ : ⋆ → Set
⟦ ι ⟧⋆ = ℕ  
⟦ σ ⇒ τ ⟧⋆ = ⟦ σ ⟧⋆ → ⟦ τ ⟧⋆

⟦_⟧ᶜ : Ctx → Set 
⟦ ε ⟧ᶜ = ⊤ 
⟦ Γ , τ ⟧ᶜ = ⟦ Γ ⟧ᶜ × ⟦ τ ⟧⋆

⟦_⟧∋_ : ∀ {Γ τ} → Γ ∋ τ → ⟦ Γ ⟧ᶜ → ⟦ τ ⟧⋆
⟦ top ⟧∋ (γ ,ᵖ t) = t 
⟦ pop i ⟧∋ (γ ,ᵖ t) = ⟦ i ⟧∋ γ 

⟦_⟧⊢_ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧ᶜ → ⟦ τ ⟧⋆
⟦ ν i ⟧⊢ γ = ⟦ i ⟧∋ γ 
⟦ ƛ t ⟧⊢ γ = λ s → ⟦ t ⟧⊢ (γ ,ᵖ s)
⟦ f · t ⟧⊢ γ = (⟦ f ⟧⊢ γ) (⟦ t ⟧⊢ γ)

--example : (ε , (ι ⇒ ι)) ⊢ λ (ν top)
--example = ? 
