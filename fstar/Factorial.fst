
module Factorial

open FStar.List
open FStar.Nat

// other dependencies

val factorial: x:nat -> Tot nat
val factorial: x:int{x>=0} -> Tot int
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

val fibonacci: n:nat -> Tot (y:nat{y>=1})
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val factorial_is_positive: x:nat -> GTot (u:unit{factorial x > 0})
let rec factorial_is_positive x =
  match x with
  | 0 -> ()
  | _ ->  factorial_is_positive (x - 1)


val length: list 'a -> Tot nat
let rec length x = match x with
  | [] -> 0
  | h::tl -> 1 + (length tl)

val append: list 'a -> list 'a -> Tot (list 'a)

let rec append x y = match x with
  | [] -> y
  | h::tl -> Cons h (append tl y)

val append_sum: x: list 'a -> y: list 'a -> GTot (u:unit{length (append x y) = length x + length y})

let rec append_sum x y = match x with
  | [] -> ()
  | h::tl -> append_sum tl y

val mem: a:'a -> l:list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | h::tl -> if a = h then true else mem a tl

val append_mem:  l1:list 'a -> l2:list 'a -> a:'a
        -> Lemma (ensures (mem a (append l1 l2)  <==>  mem a l1 || mem a l2))
let rec append_mem l1 l2 a =
  match l1 with
  | [] -> ()
  | h::tl -> append_mem tl l2 a

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]

let snoc l h = append l [h]

val snoc_cons: l:list 'a -> h:'a -> Lemma (reverse (snoc l h) = h::reverse l)
let rec snoc_cons l h = match l with
  | [] -> ()
  | hd::tl -> snoc_cons tl h

val rev_involutive: l:list 'a -> Lemma (reverse (reverse l) = l)
let rec rev_involutive l = match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; snoc_cons (reverse tl) hd


val snoc_injective: l_1:list 'a -> l_2:list 'a -> a:'a -> b:'a -> Lemma (requires (snoc l_1 a = snoc l_2 b))
																 (ensures (l_1 = l_2 && a = b))
let rec snoc_injective l_1 l_2 a b = match l_1, l_2 with
  | _::tl_1, _::tl_2 -> snoc_injective tl_1 tl_2 a b
  | _ -> ()

val rev_injective: l_1:list 'a -> l_2:list 'a
                -> Lemma (requires (reverse l_1 = reverse l_2))
                         (ensures  (l_1 = l_2))
let rec rev_injective l_1 l_2 = match l_1, l_2 with
  | a::tl_1, b::tl_2 -> snoc_injective (reverse tl_1) (reverse tl_2) a b ; rev_injective tl_1 tl_2
  | _ -> ()

type option 'a =
| None : option 'a
| Some : 'a -> option 'a

(* Prove that if find returns Some x then f x = true. Is it better to do this intrinsically or extrinsically? Do it both ways. *)
val find: f: ('a -> Tot bool) -> l:list 'a -> Tot (option 'a)
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

val find_elt_valid : f: ('a -> Tot bool) -> l:list 'a -> x:'a -> Lemma (requires find f l = Some x)
																 (ensures f x = true)
let rec find_elt_valid f l x = match l with
  | [] -> ()
  | hd::tl -> if f hd then () else find_elt_valid f tl x

val apply: f:('a -> Tot 'b) -> x: option 'a -> Tot (option 'b)
let rec apply f x = match x with
  | None -> None
  | Some a -> Some (f a)

val find_1: f: ('a -> Tot bool) -> l:list 'a -> GTot (option (x:'a{f x}))
let rec find_1 f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find_1 f tl

val fold : f: ('a -> 'b -> Tot 'b) -> l: list 'a -> a: 'b -> Tot 'b
let rec fold f l a = match l with
  | [] -> a
  | h::t -> f h (fold f t a)


val fold_left: f: ('a -> 'b -> Tot 'b) -> l: list 'a -> a: 'b -> Tot 'b
let rec fold_left f l a = match l with
  | [] -> a
  | h::t -> fold_left f t (f h a)

(*
val fold_left_cons_is_reverse: l:list 'a -> l':list 'a -> Lemma (fold_left Cons l l' = append (reverse l) l')
let rec fold_left_cons_is_reverse l l' = match l, l' with
  | h::t, h'::t' -> fold_left_cons_is_reverse t t'
  | _ -> ()
*)

val hd : l:list 'a{is_Cons l} -> Tot 'a
let hd l = match l with
  | h::t -> h

val tl : l:list 'a{is_Cons l} -> Tot (list 'a)
let tl l = match l with
  | h::t -> t

val nth : n:nat -> l:list 'a{length l > n} -> Tot 'a
let rec nth n l = match l with
		 | h::t -> if n = 0 then h else nth (n-1) t

val rev : l1:list 'a -> l2:list 'a -> Tot (list 'a) (decreases l2)
let rec rev l1 l2 =
  match l2 with
  | []     -> l1
  | hd::tl -> rev (hd::l1) tl

(*
[1;2;3]

rev 2::[1] [3] = append (append (reverse [3]) [2]) [1]

(reverse (append l [h]) = h::reverse l)
*)

val rev_append: hd: 'a -> l:list 'a -> l_1:list 'a -> Lemma (requires find f l = Some x)
													  (ensures f x = true)
let rec rev_append hd l l_1 = match l with
  | [] -> ()
  | hd::tl -> admit()

val rev_is_ok : l:list 'a -> Lemma (rev [] l = reverse l)
let rec rev_is_ok l = match l with
  | [] -> () // rev [] [] = reverse []
            // [] = []
  | hd::tl -> rev_is_ok tl // rev (hd::l_1) tl = append (reverse tl) [hd]



