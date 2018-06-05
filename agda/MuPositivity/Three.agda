
module Three where

data Three : Set where
  yes no maybe : Three

_∨_ : Three → Three → Three
yes ∨ t = yes
no ∨ yes = yes
no ∨ no = no
no ∨ maybe = maybe
maybe ∨ yes = yes
maybe ∨ no = maybe
maybe ∨ maybe = maybe

¬_ : Three → Three
¬ yes = no
¬ no = yes
¬ maybe = maybe 

_∧_ : Three → Three → Three
yes ∧ yes = yes
yes ∧ no = no
yes ∧ maybe = maybe
no ∧ t =  no
maybe ∧ yes = maybe
maybe ∧ no = no
maybe ∧ maybe = maybe 
