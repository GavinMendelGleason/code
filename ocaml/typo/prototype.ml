
open Base
       
(* 
val oo : 'a 
handy for filling holes 
*)
let oo = failwith "not Implemented"                        
       
type id = string

type ty =
  TyVar of id
| All of id * ty
| Int of unit
| Id of id
| Arr of ty * ty
| Bool of unit
| Times of ty * ty
| Plus of ty * ty

(* inductively defined types *)
type ind = (id * ty list) list
                 
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
let rec mapMaybe f l = Option.value_map ~f:f ~default:None l
     
let uncurry f (a,b) = f a b
let rec lookup i rho =
  List.find ~f:(fun (x , t) -> String.equal x i) rho
                 
let rec unify x y rho =
  match x with
    Op (o1 , tl1) ->
      (match y with
         Op (o2 , tl2) ->
         Option.find_map ~f:(foldMaybe rho (uncurry unify)) (List.zip tl1 tl2) 
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
and bind (i : id) t rho : rho option =
  match lookup i rho with
    None -> Some ((i , t)::rho)
  | Some (j , s) -> unify t s rho

type program = id * id list * obj
type programCtx = (id * ty list * ty) list
type ctx = (id * ty) list

let rec lookupPredicateType i n objGamma =
  List.find ~f:(fun (j, tylist, ty) -> String.equal i j && n = List.length tylist) objGamma 
       
let lookupTermType i gamma =
  List.find ~f:(fun (x , ty) -> String.equal i x) gamma 

let rec tyeq s t =
  match s , t with
  | TyVar id1 , TyVar id2 -> String.equal id1 id2
  | All (is1 , ty1) , All (is2 , ty2) -> String.equal is1 is2 && tyeq ty1 ty2 
  | Int () , Int () -> true
  | Id i , Id j -> String.equal i j
  | Arr (d1 , r1) , Arr (d2 , r2) -> tyeq d1 d2 && tyeq r1 r2
  | Bool () , Bool () -> true
  | Times (a1 , b1) , Times (a2 , b2) -> true
  | Plus (a1 , b1) , Plus (a2 , b2) -> true
  | _ -> false
            
(* No longer modular when we add this function, potentially could parameterise it *)
let rec opType op tl gamma objGamma =
  if String.equal op "app"
  then let tylisto = mapMaybe (fun t -> infer t gamma objGamma) tl in
       match tylisto with
         None -> None
       | Some tl -> let len = List.length tl in
                    if len = 0
                    then None
                    else if len = 1
                    then Some (List.hd_exn tl)
                    else let fty = List.hd_exn tl in
                         let xtyl = List.tl_exn tl in
                         foldMaybe (Some fty)
                                   (fun ofty vty ->
                                     match ofty with
                                     | None -> None
                                     | Some (Arr dom range) ->
                                        if tyeq dom vty
                                        then ?
                                        else None
                                     | Some _ -> None
                                   ) xtyl 
  else (* Assume 'op' is a constructor *)
    ??
            
and infer x gamma objGamma =
  match x with
    Op (o , tl) ->
    let m = List.length tl in
    (match opType o tl gamma objGamma with
       None -> None
     | Some (tylist, ty) -> oo)
  | Var i -> oo
  | Lam (i , t) -> oo
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



(* Examples 

Op[ap ; f ; g]

Op
 *) 
