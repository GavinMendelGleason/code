
module Stream

open FStar.List

// other dependencies 

val zeros: unit -> list nat
let rec zeros _ = 0 :: zeros ()
