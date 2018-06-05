
module Four where

data Four : Set where
  yes no neither both : Four

_⋎_ : Four → Four → Four
yes ⋎ yes = yes
yes ⋎ no = both
yes ⋎ neither = yes
yes ⋎ both = both
no ⋎ yes = both
no ⋎ no = no
no ⋎ neither = no
no ⋎ both = both
neither ⋎ yes = yes
neither ⋎ no = no
neither ⋎ neither = neither
neither ⋎ both = both
both ⋎ t = both 

~ : Four → Four
~ yes = no
~ no = yes
~ neither = neither
~ both = both 
