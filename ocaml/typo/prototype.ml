
type id = string

type ty =
  TyVar of id
| All of id * ty
| Int of int
| Id of id
| Bool of bool
| Times of ty * ty
| Plus of ty * ty
| Ind of (id * ty list) list

type op = id * term list
and term =
  Op of op
| Var of id
| Lam of id * term
type obj =
  OOp of op
| And of obj * obj
| Or of obj * obj
| Not of obj
type rho = (id * term) list 

let rec foldMaybe b f l =
  match l with
    [] -> Some b 
  | x :: xs ->
     (match f x b with
        None -> None
      | Some y -> foldMaybe y f xs)

let uncurry f (a,b) = f a b
let rec lookup i rho =
  match rho with
    [] -> None
  | (x , t) :: xs ->
     if x == i
     then Some t
     else lookup i xs
                 
open List
let rec unify x y rho =
  match x with
    Op (o1 , tl1) ->
      (match y with
         Op (o2 , tl2) -> foldMaybe rho (uncurry unify) (combine tl1 tl2)
       | Var j -> bind j x rho
       | Lam _ -> None)
  | Var i -> bind i y rho
  | Lam (q , t) ->
     (match y with
        Op (o2 , tl2) -> None
      | Var j -> bind j x rho
      | Lam (r , s) ->
         (match bind q (Var r) rho with
            None -> None
          | Some rho' -> unify t s rho'))
and bind id t rho =
  match lookup id rho with
    None -> Some ((id,t)::rho)
  | Some s -> unify t s rho

type program = id * id list * obj
type programType = (id * ty list * ty) list
type ctx = (id * ty) list
let rec lookupPredicate i n (objGamma : programType) =
  match objGamma with
    [] -> None
  | (j , tylist , ty) :: rho' ->
     if (i == j && n == (length tylist))
     then Some (tylist , ty)
     else lookupPredicate i n rho'

let rec infer x gamma objGamma =
  match x with
    Op (o , tl) ->
    let m = length tl in
    (match lookupPredicate o m gamma with
       None -> None
     | Some (tylist, ty) -> Some true)
  | Var i -> Some true
  | Lam (i , t) -> Some true
and checkObj x ty gamma objGamma =
  match x with
    Op (o , tl) -> true
  | Var i -> true
  | Lam (i , t) -> true
  
                                
(* 
let rec solve exp rho pro =
  match exp with
    Op (o, tl) -> lookup o 
  | _ -> rho

 *)                          
