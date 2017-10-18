module PCF where
 
open import Relation.Binary.PropositionalEquality
 
data Type : Set where
  nat : Type
  bool : Type
  _⇒_ : Type → Type → Type
 
data Ctx : Set where
  ε : Ctx
  _,_ : Ctx → Type → Ctx
 
infix 3 _∈_
data _∈_ : Type → Ctx → Set where
  here : ∀ {σ Γ} → σ ∈ Γ , σ
  there : ∀ {σ τ Γ} → σ ∈ Γ → σ ∈ Γ , τ
 
--- append
_++_ : Ctx → Ctx → Ctx
Δ ++ ε = Δ
Δ ++ (Γ , x) = (Δ ++ Γ) , x
 
--- revappend
_<><_ : Ctx → Ctx → Ctx
Γ <>< ε = Γ
Γ <>< (Δ , x) = (Γ , x) <>< Δ
 
-- Put the type at the end of the context
_·_ : Type → Ctx → Ctx
σ · ε = ε , σ
σ · (Γ , x) = (σ · Γ) , x
 
infix 3 _⊢_
data _⊢_ : Ctx → Type → Set where
  var : ∀ {Γ σ} → σ ∈ Γ →
    Γ ⊢ σ
  lam : ∀ {Γ σ τ} →
    Γ , τ ⊢ σ →
    Γ ⊢ τ ⇒ σ
  app : ∀ {Γ σ τ} →
    Γ ⊢ σ ⇒ τ → Γ ⊢ σ →
    Γ ⊢ τ
  rec : ∀ {Γ σ} →
    Γ , σ ⊢ σ →
    Γ ⊢ σ
  true : ∀ {Γ} →
    Γ ⊢ bool
  false : ∀ {Γ} →
    Γ ⊢ bool
  zero : ∀ {Γ} →
    Γ ⊢ nat
  succ : ∀ {Γ} →
    Γ ⊢ nat → Γ ⊢ nat
  case : ∀ {Γ σ} →
    Γ ⊢ nat → Γ ⊢ σ → Γ , nat ⊢ σ →
    Γ ⊢ σ
  if : ∀ {Γ σ} →
    Γ ⊢ bool → Γ ⊢ σ → Γ ⊢ σ →
    Γ ⊢ σ
 
infix 3 _⊢⟪_⊨_⟫_
data _⊢⟪_⊨_⟫_ : Ctx → Ctx → Type → Type → Set where
   ○ : ∀ {Γ σ} → Γ ⊢⟪ ε ⊨ σ ⟫ σ
   csuc : ∀ {Γ Δ σ} → Γ ⊢⟪ Δ ⊨ σ ⟫ nat → Γ ⊢⟪ Δ ⊨ σ ⟫ nat
   clam : ∀ {Γ Δ σ τ α} → Γ , σ ⊢⟪ Δ ⊨ α ⟫ τ → Γ ⊢⟪ σ · Δ ⊨ α ⟫ (σ ⇒ τ)
   capp1 : ∀ {Γ Δ σ τ α} → Γ ⊢⟪ Δ ⊨ α ⟫ (σ ⇒ τ) → Γ ⊢ σ → Γ ⊢⟪ Δ ⊨ α ⟫ τ
   capp2 : ∀ {Γ Δ σ τ α} → Γ ⊢ (σ ⇒ τ) → Γ ⊢⟪ Δ ⊨ α ⟫ σ → Γ ⊢⟪ Δ ⊨ α ⟫ τ
   crec : ∀ {Γ Δ σ τ} → Γ , σ ⊢⟪ Δ ⊨ τ ⟫ σ → Γ ⊢⟪ σ · Δ ⊨ τ ⟫ σ
   ccase1 : ∀ {Γ Δ σ α} → Γ ⊢⟪ Δ ⊨ α ⟫ nat → Γ ⊢ σ → Γ , nat ⊢ σ → Γ ⊢⟪ Δ ⊨ α ⟫ σ
   ccase2 : ∀ {Γ Δ σ α} → Γ ⊢ nat → Γ ⊢⟪ Δ ⊨ α ⟫ σ → Γ , nat ⊢ σ → Γ ⊢⟪ Δ ⊨ α ⟫ σ
   ccase3 : ∀ {Γ Δ σ α} → Γ ⊢ nat → Γ ⊢ σ → Γ , nat ⊢⟪ Δ ⊨ α ⟫ σ → Γ ⊢⟪ nat · Δ ⊨ α ⟫ σ
   cif1 : ∀ {Γ Δ σ α} → Γ ⊢⟪ Δ ⊨ α ⟫ bool → Γ ⊢ σ → Γ ⊢ σ → Γ ⊢⟪ Δ ⊨ α ⟫ σ
   cif2 : ∀ {Γ Δ σ α} → Γ ⊢ bool → Γ ⊢⟪ Δ ⊨ α ⟫ σ → Γ ⊢ σ → Γ ⊢⟪ Δ ⊨ α ⟫ σ
   cif3 : ∀ {Γ Δ σ α} → Γ ⊢ bool → Γ ⊢ σ → Γ ⊢⟪ Δ ⊨ α ⟫ σ → Γ ⊢⟪ Δ ⊨ α ⟫ σ
 
++·assoc : ∀ Γ Δ σ → Γ ++ (σ · Δ) ≡ (Γ , σ) ++ Δ
++·assoc Γ ε σ = refl
++·assoc Γ (Δ , x) σ with ++·assoc Γ Δ σ
++·assoc Γ (Δ , x) σ | res = cong₂ _,_ res refl
 
_⟦_⟧ : ∀ {Γ Δ τ α} → Γ ⊢⟪ Δ ⊨ α ⟫ τ → Γ ++ Δ ⊢ α → Γ ⊢ τ
○ ⟦ t ⟧ = t
csuc e ⟦ t ⟧ = succ (e ⟦ t ⟧)
clam {Γ} {Δ} {σ} e ⟦ t ⟧ rewrite ++·assoc Γ Δ σ = lam (e ⟦ t ⟧)
capp1 e x ⟦ t ⟧ = app (e ⟦ t ⟧) x
capp2 x e ⟦ t ⟧ = app x (e ⟦ t ⟧)
crec {Γ} {Δ} {σ} e ⟦ t ⟧ rewrite ++·assoc Γ Δ σ = rec (e ⟦ t ⟧)
ccase1 e x x₁ ⟦ t ⟧ = case (e ⟦ t ⟧) x x₁
ccase2 x e x₁ ⟦ t ⟧ = case x (e ⟦ t ⟧) x₁
ccase3 {Γ} {Δ} x x₁ e ⟦ t ⟧ rewrite ++·assoc Γ Δ nat = case x x₁ (e ⟦ t ⟧)
cif1 e x x₁ ⟦ t ⟧ = if (e ⟦ t ⟧) x x₁
cif2 x e x₁ ⟦ t ⟧ = if x (e ⟦ t ⟧) x₁
cif3 x x₁ e ⟦ t ⟧ = if x x₁ (e ⟦ t ⟧)
 
Ren Sub : Ctx → Ctx → Set
Ren Γ Δ = ∀ {τ} → (τ ∈ Γ) → (τ ∈ Δ)
Sub Γ Δ = ∀ {τ} → (τ ∈ Γ) → (Δ ⊢ τ)
 
-- shiftable substitutions
Shub : Ctx → Ctx → Set
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)
 
wksh : ∀ {Γ Δ τ} → Shub Γ Δ → Shub (Γ , τ) (Δ , τ)
wksh θ = λ Ξ x → θ (Ξ , _) x
 
_//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
θ // var x = θ ε x
θ // lam {Γ} {σ} {τ} p = lam (wksh θ // p)
θ // app p p₁ = app (θ // p) (θ // p₁)
θ // rec {Γ} p = rec (wksh θ // p)
θ // true = true
θ // false = false
θ // zero = zero
θ // succ p = succ (θ // p)
θ // case p p₁ p₂ = case (θ // p) (θ // p₁) (wksh θ // p₂)
θ // if p p₁ p₂ = if (θ // p) (θ // p₁) (θ // p₂)
 
wkr : ∀ {Γ Δ τ} → Ren Γ Δ → Ren (Γ , τ) (Δ , τ)
wkr r here = here
wkr r (there x) = there (r x)
 
ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren r ε x = var (r x)
ren r (Γ , τ) x = ren (wkr r) Γ x
 
wks : ∀ {Γ Δ τ} → Sub Γ Δ → Sub (Γ , τ) (Δ , τ)
wks θ here = var here
wks θ (there x) = ren there // θ x
 
sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub θ ε = θ
sub θ (Γ , x₁) = sub (wks θ) Γ
 
_-_ : ∀ {τ} Γ → (p : τ ∈ Γ) → Ctx
ε - ()
(Γ , τ) - here = Γ
(Γ , x) - there p = (Γ - p) , x
 
_≠_ : ∀ {Γ τ} → (p : τ ∈ Γ) → Ren (Γ - p) Γ
here ≠ q = there q
there p ≠ here = here
there p ≠ there q = there (p ≠ q)
 
data comp {Γ τ} (p : τ ∈ Γ) : ∀ {σ} → (q : σ ∈ Γ) → Set where
  same : comp p p
  diff : ∀ {τ} (q : τ ∈ Γ - p) → comp p (p ≠ q)
 
_≟_ : ∀ {Γ τ σ} → (p : τ ∈ Γ) → (q : σ ∈ Γ) → comp p q
here ≟ here = same
here ≟ there y = diff y
there x ≟ here = diff here
there x ≟ there y with x ≟ y
there x ≟ there .x | same = same
there x ≟ there .(x ≠ q) | diff q = diff (there q)
 
renTerm : ∀ {Γ Δ σ} → Ren Γ Δ → Γ ⊢ σ → Δ ⊢ σ
renTerm r (var x) = var (r x)
renTerm r (lam t) = lam (renTerm (wkr r) t)
renTerm r (app t t₁) = app (renTerm r t) (renTerm r t₁)
renTerm r (rec t) = rec (renTerm (wkr r) t)
renTerm r true = true
renTerm r false = false
renTerm r zero = zero
renTerm r (succ t) = succ (renTerm r t)
renTerm r (case t t₁ t₂) = case (renTerm r t) (renTerm r t₁) (renTerm (wkr r) t₂)
renTerm r (if t t₁ t₂) = if (renTerm r t) (renTerm r t₁) (renTerm r t₂)
 
⟨_↦_⟩_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ - x ⊢ σ → Γ ⊢ τ → Γ - x ⊢ τ
⟨ x ↦ s ⟩ var y with x ≟ y
⟨ x ↦ s ⟩ var .x | same = s
⟨ x ↦ s ⟩ var .(x ≠ q) | diff q = var q
⟨ x ↦ s ⟩ lam t with ⟨ there x ↦ renTerm there s ⟩ t
⟨ x ↦ s ⟩ lam t | res = lam res
⟨ x ↦ s ⟩ app t t₁ = app (⟨ x ↦ s ⟩ t) (⟨ x ↦ s ⟩ t₁)
⟨ x ↦ s ⟩ rec t = rec (⟨ there x ↦ renTerm there s ⟩ t) -- (⟨ x ↦ s ⟩ t)
⟨ x ↦ s ⟩ true = true
⟨ x ↦ s ⟩ false = false
⟨ x ↦ s ⟩ zero = zero
⟨ x ↦ s ⟩ succ t = succ (⟨ x ↦ s ⟩ t)
⟨ x ↦ s ⟩ case t t₁ t₂ = case (⟨ x ↦ s ⟩ t) (⟨ x ↦ s ⟩ t₁) (⟨ there x ↦ renTerm there s ⟩ t₂)
⟨ x ↦ s ⟩ if t t₁ t₂ = if (⟨ x ↦ s ⟩ t) (⟨ x ↦ s ⟩ t₁) (⟨ x ↦ s ⟩ t₂)
 
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Unit
open import Data.Empty
 
WHNF? : ∀ {Γ τ} → (p : Γ ⊢ τ) → Set
WHNF? (var x) = ⊥
WHNF? (lam p) = ⊤
WHNF? (app p p₁) = ⊥
WHNF? (rec p) = ⊥
WHNF? true = ⊤
WHNF? false = ⊤
WHNF? zero = ⊤
WHNF? (succ p) = ⊤
WHNF? (case p p₁ p₂) = ⊥
WHNF? (if p p₁ p₂) = ⊥
 
data Stop (Γ : Ctx) (τ : Type) : Set where
  var : τ ∈ Γ → Stop Γ τ
  app : ∀ {σ} → Stop Γ (σ ⇒ τ) → Γ ⊢ σ → Stop Γ τ
  case : Stop Γ nat → Γ ⊢ τ → Γ , nat ⊢ τ → Stop Γ τ
  if : Stop Γ bool → Γ ⊢ τ → Γ ⊢ τ → Stop Γ τ
 
-- Experiments have no context extension
infix 4 _⊢⟪_⟫_
data _⊢⟪_⟫_ : Ctx → Type → Type → Set where
   e○ : ∀ {Γ σ} → Γ ⊢⟪ σ ⟫ σ
   eapp : ∀ {Γ σ τ α} → Γ ⊢⟪ α ⟫ (σ ⇒ τ) → Γ ⊢ σ → Γ ⊢⟪ α ⟫ τ
   ecase : ∀ {Γ σ α} → Γ ⊢⟪ α ⟫ nat → Γ ⊢ σ → Γ , nat ⊢ σ → Γ ⊢⟪ α ⟫ σ
   eif : ∀ {Γ σ α} → Γ ⊢⟪ α ⟫ bool → Γ ⊢ σ → Γ ⊢ σ → Γ ⊢⟪ α ⟫ σ
 
_⟦_⟧exp : ∀ {Γ τ α} → Γ ⊢⟪ α ⟫ τ → Γ ⊢ α → Γ ⊢ τ
e○ ⟦ t ⟧exp = t
eapp ex x ⟦ t ⟧exp = app (ex ⟦ t ⟧exp) x
ecase ex x x₁ ⟦ t ⟧exp = case (ex ⟦ t ⟧exp) x x₁
eif ex x x₁ ⟦ t ⟧exp = if (ex ⟦ t ⟧exp) x x₁
 
Redux? : ∀ {Γ τ} → (p : Γ ⊢ τ) → Set
Redux? (var x) = ⊤
Redux? (lam p) = ⊤
Redux? (app p p₁) = ⊥
Redux? (rec p) = ⊤
Redux? true = ⊤
Redux? false = ⊤
Redux? zero = ⊤
Redux? (succ p) = ⊤
Redux? (case p p₁ p₂) = ⊥
Redux? (if p p₁ p₂) = ⊥
 
open import Data.Product renaming (_,_ to _*_)
 
factor : ∀ {Γ σ} → (p : Γ ⊢ σ) → Σ[ τ ∈ Type ] Σ[ e ∈ Γ ⊢⟪ τ ⟫ σ ] Σ[ t ∈ Γ ⊢ τ ] (e ⟦ t ⟧exp ≡ p × Redux? t )
factor (var {σ = σ} x) = σ * e○ * var x * refl * tt
factor (lam {σ = σ} {τ = τ} p) = τ ⇒ σ * e○ * lam p * refl * tt
factor (app p p₁) with factor p
factor (app .(proj₂ ⟦ proj₃ ⟧exp) p₁) | proj₁ * proj₂ * proj₃ * refl * proj₅ = proj₁ * eapp proj₂ p₁ * proj₃ * refl * proj₅
factor (rec {σ = σ} p) = σ * e○ * rec p * refl * tt
factor true = bool * e○ * true * refl * tt
factor false = bool * e○ * false * refl * tt
factor zero = nat * e○ * zero * refl * tt
factor (succ p) = nat * e○ * succ p * refl * tt
factor (case p p₁ p₂) with factor p
factor (case .(proj₂ ⟦ proj₃ ⟧exp) p₁ p₂) | proj₁ * proj₂ * proj₃ * refl * proj₅ = proj₁ * ecase proj₂ p₁ p₂ * proj₃ * refl * proj₅
factor (if p p₁ p₂) with factor p
factor (if .(proj₂ ⟦ proj₃ ⟧exp) p₁ p₂) | proj₁ * proj₂ * proj₃ * refl * proj₅ = proj₁ * eif proj₂ p₁ p₂ * proj₃ * refl * proj₅
 
data _↝_ {Γ} {τ} : (p : Γ ⊢ τ) (q : Γ ⊢ τ) → Set where
  β : ∀ {σ} {p : Γ , σ ⊢ τ} {r : Γ ⊢ σ} → (app (lam p) r) ↝ (⟨ here ↦ r ⟩ p)
  Ezero : ∀ {p : Γ ⊢ τ} {q : Γ , nat ⊢ τ} → case zero p q ↝ p
  Esucc : ∀ {n : Γ ⊢ nat} {p : Γ ⊢ τ} {q : Γ , nat ⊢ τ} → (case (succ n) p q) ↝ (⟨ here ↦ n ⟩ q)
  Etrue : ∀ {p : Γ ⊢ τ} {q : Γ ⊢ τ} → if true p q ↝ p
  Efalse : ∀ {p : Γ ⊢ τ} {q : Γ ⊢ τ} → if false p q ↝ q
  Erec : ∀ {p : Γ , τ ⊢ τ} → (rec p) ↝ (⟨ here ↦ rec p ⟩ p)
  F : ∀ {α} (e : Γ ⊢⟪ α ⟫ τ) {t t' : Γ ⊢ α} {p : Γ ⊢ τ} → e ⟦ t ⟧exp ≡ p → t ↝ t' → p ↝ (e ⟦ t' ⟧exp)
 
open import Data.Sum
 
progressLemma : ∀ {τ} → (p : ε ⊢ τ) → (WHNF? p ⊎ (Σ[ q ∈ ε ⊢ τ ] p ↝ q))
progressLemma (var ())
progressLemma (lam p) = inj₁ tt
progressLemma (app p p₁) with progressLemma p
progressLemma (app (var x) p₁) | inj₁ ()
progressLemma (app (lam p) p₁) | inj₁ x = inj₂ (⟨ here ↦ p₁ ⟩ p * β)
progressLemma (app (app p p₁) p₂) | inj₁ ()
progressLemma (app (rec p) p₁) | inj₁ ()
progressLemma (app (case p p₁ p₂) p₃) | inj₁ ()
progressLemma (app (if p p₁ p₂) p₃) | inj₁ ()
progressLemma (app p p₁) | inj₂ (t' * rel) = inj₂ (app t' p₁ * F (eapp e○ p₁) refl rel)
progressLemma (rec p) = inj₂ (⟨ here ↦ rec p ⟩ p * Erec)
progressLemma true = inj₁ tt
progressLemma false = inj₁ tt
progressLemma zero = inj₁ tt
progressLemma (succ p) = inj₁ tt
progressLemma (case p p₁ p₂) with progressLemma p
progressLemma (case (var x) p₁ p₂) | inj₁ ()
progressLemma (case (app p p₁) p₂ p₃) | inj₁ ()
progressLemma (case (rec p) p₁ p₂) | inj₁ ()
progressLemma (case zero p₁ p₂) | inj₁ x = inj₂ (p₁ * Ezero)
progressLemma (case (succ p) p₁ p₂) | inj₁ x = inj₂ (⟨ here ↦ p ⟩ p₂ * Esucc)
progressLemma (case (case p p₁ p₂) p₃ p₄) | inj₁ ()
progressLemma (case (if p p₁ p₂) p₃ p₄) | inj₁ ()
progressLemma (case p p₁ p₂) | inj₂ (t' * rel) = inj₂ (case t' p₁ p₂ * (F (ecase e○ p₁ p₂) refl rel))
progressLemma (if p p₁ p₂) with progressLemma p
progressLemma (if (var x) p₁ p₂) | inj₁ ()
progressLemma (if (app p p₁) p₂ p₃) | inj₁ ()
progressLemma (if (rec p) p₁ p₂) | inj₁ ()
progressLemma (if true p₁ p₂) | inj₁ x = inj₂ (p₁ * Etrue)
progressLemma (if false p₁ p₂) | inj₁ x = inj₂ (p₂ * Efalse)
progressLemma (if (case p p₁ p₂) p₃ p₄) | inj₁ ()
progressLemma (if (if p p₁ p₂) p₃ p₄) | inj₁ ()
progressLemma (if p p₁ p₂) | inj₂ (t' * rel) = inj₂ (if t' p₁ p₂ * F (eif e○ p₁ p₂) refl rel)
 
open import Coinduction
 
data _⊢_↝*_ : ∀ Γ {τ} (p : Γ ⊢ τ) (q : Γ ⊢ τ) → Set where
  ↝*val : ∀ Γ {τ} → (p : Γ ⊢ τ) → WHNF? p → Γ ⊢ p ↝* p
  ↝*step : ∀ Γ {τ} → (p q s : Γ ⊢ τ) → ∞ (Γ ⊢ p ↝* q) → q ↝ s → Γ ⊢ p ↝* s 
 
try : ε ⊢ true ↝* true
try = ↝*val ε true tt

data _⊢_⇓ : ∀ Γ {τ} (p : Γ ⊢ τ) → Set where
  ⇓val : ∀ Γ {τ} → (p : Γ ⊢ τ) → Σ (Γ ⊢ τ) (λ q → Γ ⊢ p ↝* q × WHNF? q) → Γ ⊢ p ⇓

-- _□_ : 

{-
data _·_⊢_≾_Ctx : ∀ Γ Δ {α} (t t' : Γ ++ Δ ⊢ α) → Set where
  base : ∀ Γ Δ {α} (t t' : Γ ++ Δ ⊢ α) →
                    (∀ (c : Γ ⊢⟪ Δ ⊨ α ⟫ bool) → Γ ⊢ (c ⟦ t ⟧) ↝* true → Γ ⊢ (c ⟦ t' ⟧) ↝* true) →
                    Γ · Δ ⊢ t ≾ t' Ctx
 
data _⊢_≾_Exp : ∀ Γ {α} (t t' : Γ ⊢ α) → Set where
  base : ∀ Γ {α} (t t' : Γ ⊢ α) →
                  (∀ (e : Γ ⊢⟪ α ⟫ bool) → Γ ⊢ (e ⟦ t ⟧exp) ↝* true → Γ ⊢ (e ⟦ t' ⟧exp) ↝* true) →
                  Γ ⊢ t ≾ t' Exp

exp⇒ctx : ∀ τ α (e : ε ⊢⟪ α ⟫ τ) (t : ε ⊢ α) → ε ⊢ e ⟦ t ⟧exp ↝* p → Σ (ε ⊢⟪ ε ⊨ α ⟫ τ) (λ c → ε ⊢ c ⟦ t ⟧ ↝* true)
exp⇒ctx τ α e p = ? 
-}


{- 
Some inspiration here: https://www.cl.cam.ac.uk/teaching/0910/L16/semhl-15-ann.pdf
-}

{- Demonstrate that they are equivalent? 

exp⇒ctx : ∀ τ α (e : ε ⊢⟪ α ⟫ τ) (t : ε ⊢ α) → ε ⊢ e ⟦ t ⟧exp ↝* p → Σ (ε ⊢⟪ ε ⊨ α ⟫ τ) (λ c → ε ⊢ c ⟦ t ⟧ ↝* true)
exp⇒ctx τ α e p = ? 

ExperimentSufficiencyLemma : ∀ α (t t' : ε ⊢ α) → ε · ε ⊢ t ≾ t' Ctx → ε ⊢ t ≾ t' Exp
ExperimentSufficiencyLemma nat t t' (base .ε .ε .t .t' x) = base ε t t' (λ e x₁ → {!!})
ExperimentSufficiencyLemma bool t t' (base .ε .ε .t .t' x) = base ε {!!} {!!} (λ e x₁ → {!!})
ExperimentSufficiencyLemma (α ⇒ α₁) t t' (base .ε .ε .t .t' x) = base ε {!!} {!!} (λ e x₁ → {!!})

ContextSufficiencyLemma : ∀ Γ Δ α (t t' : Γ ++ Δ ⊢ α) → Γ · Δ ⊢ t ≾ t' Ctx → (Γ ++ Δ) ⊢ t ≾ t' Exp
ContextSufficiencyLemma Γ Δ α t t' (base .Γ .Δ .t .t' x) = 
  let h e r = {!!} in base (Γ ++ Δ) t t' h
  where telescope : ∀ Γ Δ α → Γ ⊢⟪ Δ ⊨ α ⟫ bool
        telescope Γ Δ α = {! !}
        transmuteExperiment : ∀ Γ Δ t (e : (Γ ++ Δ) ⊢⟪ α ⟫ bool) → (Γ ++ Δ) ⊢ e ⟦ t ⟧exp ↝* true → Σ (Γ ⊢⟪ Δ ⊨ α ⟫ bool) (λ c → Γ ⊢ c ⟦ t ⟧ ↝* true)
        transmuteExperiment Γ Δ t₁ e red = {!!}
-}
