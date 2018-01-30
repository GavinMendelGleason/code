module BinTree where 

-- open import 

data True : Set where 
  tt : True

data False : Set where 

data _||_ (A B : Set) : Set where 
  inl : A → A || B 
  inr : B → A || B

data _&_ (A B : Set) : Set where 
  <_,_> : A → B → A & B

infixl 6 _&_

data Exists (A : Set) (B : A → Set) : Set where 
  exists : (a : A) → B a → Exists A B

data _==_ {A : Set} : A → A → Set where 
  refl : (a : A) → a == a


subst : {A : Set} → {C : A → Set} → (a a' : A) → a == a' → C a → C a'
subst .a .a (refl a) p = p

postulate A : Set
postulate _<=_ : A → A → Set 
postulate tot : ∀(a b : A) → (a <= b) || (b <= a)
postulate antisym : ∀{a b} → (a <= b) → (b <= a) → a == b
postulate ref : ∀(a : A) → (a <= a)
postulate trans : ∀{a b c} → (a <= b) → (b <= c) → (a <= c)

data BinTree : Set where 
  lf : BinTree
  nd : A → BinTree → BinTree → BinTree

all-leq : BinTree → A → Set 
all-leq lf a = True
all-leq (nd x bl br) a = (x <= a) & (all-leq bl a) & (all-leq br a)

all-geq : BinTree → A → Set 
all-geq lf a = True
all-geq (nd x bl br) a = (a <= x) & (all-geq bl a) & (all-geq br a)

Sorted : BinTree → Set 
Sorted lf = True
Sorted (nd x bl br) = ((all-geq bl x) & Sorted bl) & 
                      ((all-leq br x) & Sorted br)

insert : A → BinTree → BinTree 
insert a lf = nd a lf lf
insert a (nd b bl br) with tot a b 
... | inl _ = nd b bl (insert a br)
... | inr _ = nd b (insert a bl) br

--all-leq-trans : ∀ (a b : A) → (br : BinTree) → b <= a → all-leq br b → all-leq br a 
--all-leq-trans a b lf _ tt = tt
--all-leq-trans a b (nd x bl' br') p < < xle , al > , ar >  = 
--  < < trans xle p , all-leq-trans a b bl' p al > , all-leq-trans a b br' p ar > 

all-leq-trans : ∀ (a b : A) → (br : BinTree) → b <= a → all-leq br b → all-leq br a 
all-leq-trans a b lf _ tt = tt
all-leq-trans a b (nd x bl' br') p < < xle , al > , ar >  = 
  < < trans xle p , all-leq-trans a b bl' p al > , all-leq-trans a b br' p ar > 

all-geq-trans : ∀ (a b : A) → (br : BinTree) → a <= b → all-geq br b → all-geq br a 
all-geq-trans a b lf _ tt = tt
all-geq-trans a b (nd x bl' br') p < < xge , al > , ar >  = 
  < < trans p xge , all-geq-trans a b bl' p al > , all-geq-trans a b br' p ar > 

insert' : A → (t : BinTree) → Sorted t → Exists BinTree (λ t' → Sorted t')
insert' a lf p = exists (nd a lf lf) < < tt , tt > , < tt , tt > >
insert' a (nd b bl br) < < ag , psl > , < al , psr > > with tot a b 
insert' a (nd b bl br) < < ag , psl > , < al , psr > > | inl p1 with insert' a br psr
insert' a (nd b bl br) < < ag , psl > , < al , psr > > | inl p1 | exists br' p' = 
  exists (nd b bl br') < < ag , psl > , < all-leq-trans b {!!} br' {!!} {!!} , p' > >
insert' a (nd b bl br) < < ag , psl > , < al , psr > > | inr p1 with insert' a bl psl
insert' a (nd b bl br) < < ag , psl > , < al , psr > > | inr p1 | exists bl' p' = 
  exists (nd b bl' br) < < all-geq-trans {!!} {!!} bl' {!!} {!!} , p' > , < al , psr > >

