
open import Data.Bool

data Top : Set where
  tt : Top

data Bot : Set where

inhabited : Bool -> Set
inhabited true = Top 
inhabited false = Bot
