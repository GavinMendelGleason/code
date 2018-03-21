
module Example2 where 

data ℕ : Set where 
  zero : ℕ 
  succ : ℕ → ℕ 

{-
data Maybe (A : Set) : Set where 
  nothing : Maybe A 
  just : A → Maybe A
-} 

data _+_ (A B : Set) : Set where 
  inl : A → A + B
  inr : B → A + B

data 𝟙 : Set where 
  u : 𝟙

data [_] (A : Set) : Set where 
  ε : [ A ] 
  _∷_ : A → [ A ] → [ A ] 

Maybe : ∀ A → Set 
Maybe A = 𝟙 + A

example : Maybe ℕ 
example = inl u 


example2 : Maybe ℕ 
example2 = inr zero

hd : ∀ {A : Set} → [ A ] → Maybe A
hd ε = inl u
hd (x ∷ x₁) = inr x

data ⊥ : Set where 

one : ⊥ → ⊥ 
one ()  

-- μ X . 1 + X 


