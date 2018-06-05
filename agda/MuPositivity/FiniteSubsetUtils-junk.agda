
{-
_#_⟨_⟩ : ∀ {C : Set} (S : List C) (x : C) (eq : DecEq C) → Σ[ ys ∈ List C ] ∀ a → a ∈L S → a ∈L ys ⊎ a ≡ x × a ∉L ys
[] # x ⟨ eq ⟩ = [] , (λ x₁ → inj₁)
(x ∷ S) # x₁ ⟨ eq ⟩ with S # x₁ ⟨ eq ⟩ | eq x x₁ 
(x ∷ S) # .x ⟨ eq ⟩ | ys , f | yes refl = ys , (λ a a∈x∷S → let p = f a in {!!})
  where aux : ∀ {C : Set} {a : C} {x S ys} → a ∈L (x ∷ S) → ((a ∈L S) → a ∈L ys ⊎ (a ≡ x) × (a ∉L ys)) → a ∈L ys ⊎ (a ≡ x) × a ∉L ys
        aux here q = {!!}
        aux (there P) q = {!!}
(x ∷ S) # x₁ ⟨ eq ⟩ | ys , f | no ¬p = x ∷ S , (λ x₂ → inj₁) 

{-
(x ∷ S) ⊂L T →  S ⊂L T - [ x ]
S ⊂L proj₁ (T ─ x ∷ [] ⟨ eq ⟩)
-}

⊂⇒Σ⊂ : ∀ {C : Set}{eq : DecEq C} → (S : List C) → (T : List C) → S ⊂L T → NoDupInd S → (S Σ⊂L T)
⊂⇒Σ⊂ [] [] (proj₁ , proj₂) nd = ⊥-elim (proj₂ (λ _ z → z))
⊂⇒Σ⊂ [] (x ∷ T) P nd = (λ x₁ → λ ()) , x , here , (λ ())
⊂⇒Σ⊂ {eq = eq} (x ∷ S) T P nd with eq2in eq x T
⊂⇒Σ⊂ {eq = eq} (x ∷ S) T (sub , notsub) (x₁ ::: nd) | yes p with ⊂⇒Σ⊂ {eq = eq} S (proj₁ (T ─ (x ∷ []) ⟨ eq ⟩ )) {! !} nd
⊂⇒Σ⊂ {eq = eq} (x ∷ S) T (sub , notsub)  (x₁ ::: nd) | yes p | S⊆T , y , y' , y'∉S = {!!} 
⊂⇒Σ⊂ (x ∷ S) T (sub , notsub) nd | no ¬p = sub , x , sub x here , (λ x₁ → ¬p (sub x x₁))
-}
{- proj₃ , y , {!!} , (λ x₁ → let p = proj₆ x in {!p!} )

open import Data.Sum

open import Data.Unit

⊂⇒Σ⊂ : ∀ {C : Set}{eq : DecEq C} →
     (S : FiniteSubSet C eq false) → (T : FiniteSubSet C eq false) →
     S ⊂ T → (S Σ⊂ T)
⊂⇒Σ⊂ (fs-nojunk []) (fs-nojunk []) (proj₁ , proj₂) = ⊥-elim (proj₂ (λ s z → z))
⊂⇒Σ⊂ (fs-nojunk []) (fs-nojunk (x ∷ els₁)) (proj₁ , proj₂) = x , proj₁ , here , (λ ())
⊂⇒Σ⊂ (fs-nojunk (x ∷ els)) (fs-nojunk []) (proj₁ , proj₂) = x , proj₁ , proj₁ x here , (λ x₁ → proj₂ (λ s → λ ()))
⊂⇒Σ⊂ {eq = eq} (fs-nojunk (x ∷ els)) (fs-nojunk (x₁ ∷ els₁)) (proj₁ , proj₂) with eq x x₁
⊂⇒Σ⊂ (fs-nojunk (x ∷ els)) (fs-nojunk (.x ∷ els₁)) (proj₁ , proj₂) | yes refl = {!!}
⊂⇒Σ⊂ (fs-nojunk (x ∷ els)) (fs-nojunk (x₁ ∷ els₁)) (proj₁ , proj₂) | no ¬p = x₁ , proj₁ , here , (λ x₁∈x∷els → {!!})
-}

{-  ,
                                                                                                                                                -}
--⊂⇒Σ⊂ (fs-nojunk (x₁ ∷ els)) (fs-nojunk els₁) (sub , nosub) | it y x | res  = {!!}

{-
⊂⇒Σ⊂ (fs-nojunk (x₁ ∷ els)) (fs-nojunk els₁ {nd₂}) (proj₁ , proj₂) | res | res₂ = {!!}

-}
{- 
⊂⇒Σ⊂ (fs-nojunk (x₁ ∷ els)) (fs-nojunk els₁) (proj₁ , proj₂) | it y x | res = {!!} -}


{-

yes p  
⊂⇒Σ⊂ (fs-nojunk (x ∷ els)) (fs-nojunk els₁) (proj₁ , proj₂) | res | yes p | res₂ = {!!}

-} 
--with ⊂⇒Σ⊂ (fs-nojunk els {{!!}}) (fs-nojunk els₁ {nd₂})
 --                                                                                         ((λ x₁ x₂ → proj₁ x₁ (there x₂)) ,
 --                                                                                          (λ x₁ → proj₂ (λ s z → there (x₁ s z))))
--⊂⇒Σ⊂ (fs-nojunk (x ∷ els) {nd₁}) (fs-nojunk els₁ {nd₂}) (proj₁ , proj₂) | res =  ? | res₂ = {!!}
--⊂⇒Σ⊂ (fs-nojunk (x ∷ els)) (fs-nojunk els₁) (proj₁ , proj₂) | res = {!!}

{-

with ⊂⇒Σ⊂ {C} {eq} (fs-nojunk {C} {eq} els {{!!}}) (fs-nojunk els₁) ((λ x₁ x₂ → proj₁ x₁ (there x₂)) ,
                                                                                                                     (λ x₁ → proj₂ (λ s z → there (x₁ s z))))

⊂⇒Σ⊂ (fs-nojunk (x ∷ els)) (fs-nojunk els₁) (proj₁ , proj₂) | yes p | res | proj₃ , sub , innit , notin = proj₃ , proj₁ , innit , {!weaken¬⊆!}

⊂ND⇒Σ : ∀ {C : Set}{eq : DecEq C} → (S : ListableNoDup C) → (T : ListableNoDup C) → S ⊂ND T → ∣ S ∣ND < ∣ T ∣ND
⊂ND⇒Σ ([] , proj₁) ([] , proj₄) (proj₂ , proj₃) = ⊥-elim (proj₃ (λ x z → z))
⊂ND⇒Σ ([] , proj₁) (x ∷ proj₃ , proj₄) (proj₂ , proj₅) = s≤s z≤n
⊂ND⇒Σ (x ∷ proj₁ , proj₂) ([] , proj₄) (proj₃ , proj₅) = ⊥-elim (proj₅ (λ p ()))
⊂ND⇒Σ (x ∷ xs , proj₂ , x₁ ::: proj₃) (x₂ ∷ ys , proj₁ , x₃ ::: proj₅) (proj₄ , proj₆) with ⊂ND⇒Σ (xs , (λ x → {!!}) , proj₃) (ys , {!!} , proj₅) {!!}
⊂ND⇒Σ (x ∷ xs , proj₂ , x₁ ::: proj₃) (x₂ ∷ ys , proj₁ , x₃ ::: proj₅) (proj₄ , proj₆) | res = {!!}


with ⊂ND⇒Σ (xs , (λ x → {!!}) , proj₃) (ys , {!!} , proj₅) {!!} 
⊂ND⇒Σ (x ∷ xs , proj₂ , x₁ ::: proj₃) (x₂ ∷ ys , proj₁ , x₃ ::: proj₅) Q | res = {!!}
-}

{-


notEmptySubset : ∀ {C : Set}{eq : DecEq C} (S T : List C) → S ⊂L T → proj₁ (T ─ S ⟨ eq ⟩) ≢ []
notEmptySubset [] [] S⊂T x = proj₂ S⊂T (λ x₁ x₂ → x₂)
notEmptySubset {eq = eq} [] (x ∷ T) (proj₁ , proj₂) x₁ with (x ∷ T) ─ [] ⟨ eq ⟩
notEmptySubset [] (x ∷ T) (proj₁ , proj₂) () | res
notEmptySubset (x ∷ S) [] S⊂T x₁ = proj₂ S⊂T (λ x₂ → λ ())
notEmptySubset {eq = eq} (x ∷ S) (x₁ ∷ T) S⊂T x₂ with (x ∷ T) ─ (x₁ ∷ S) ⟨ eq ⟩
notEmptySubset (x ∷ S) (x₁ ∷ T) (proj₃ , proj₄) x₂ | proj₁ , proj₂ = let p = proj₂ x in {!!} 

ExtendLemma : ∀ {C : Set} (x y : C) T S → y ∈L T → x ∉L S → x ∈L T → y ∉L S → y ∉L (x ∷ S)
ExtendLemma y .y T S y∈T x∉S x∈T y∉S here = {!!}
ExtendLemma x y T S y∈T x∉S x∈T y∉S (there y∈x) = y∈x ↯ y∉S 


-}
