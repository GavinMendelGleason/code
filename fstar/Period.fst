type list 'a =
  | Nil  : list 'a
  | Cons : hd:'a -> tl:list 'a -> list 'a

type stream 'a = 
  | SNil 
  | SCons : hd:'a -> (unit -> tl:stream 'a) -> stream 'a

val zero_chunk : nat -> list 'a 
let rec n = if n == 0 then Nil else Cons 0 (zero_chunk (n-1))

val zero_chunks : nat -> stream 'a
let rec zero_chunks n = Scons (zero_chunk n) (fun _ => zero_chunks n)

val zero_chunks_correct : n:nat -> l:list 'a -> Lemma zero_chunks
