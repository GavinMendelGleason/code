
open import Level hiding (suc)
open import Coinduction
open import Data.Nat

mutual

 data Block (A : Set) : ℕ → Set where
   nil : Block A 0
   cons : ∀ {n} → A → Block A (suc n) → Block A n
  
 data PeriodStream (A : Set) (period : ℕ) : Set where
   end : PeriodStream A period
   next : Block A period → ∞ (PeriodStream A period) → PeriodStream A period
