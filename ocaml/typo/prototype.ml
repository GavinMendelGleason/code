
open Base
       
type id = string
type var = string * int
  
type ty =
  | TyVar of id
  | Arr of ty * ty
  | T of unit
  | Int of unit
  | Bool of unit
  | Times of ty * ty
  | Plus of ty * ty

(* inductively defined types *)
type inductiveName = id
and inductiveTypeParameters = id list
and constructors = (id * ty) list
                             
type ind = inductiveName * inductiveTypeParameters * constructors

type typedefCtx = ind list
       
type op = id * term list
and term =
  | Fun of op
  | App of term * term list (* Oppa Krivine style? *)
  | BVar of var
  | FVar of var
  | Lam of id * term
type obj =
  | Op of term
  | And of obj list
  | Or of obj list
  | Not of obj
           
type rho = (var * term) list 

open Printf
let v = ref 0
let fresh (x : id) : var =
  v := !v + 1 ;
  (x ^ (Printf.sprintf "%d" !v), !v)

let printVar ((name , i) : var) : string = Printf.sprintf "%s.%d" name i
        
let up ((name , i) : var)  (n : int) : var = (name , i+n)
let down ((name , i) : var) (n : int) : var = if Int.equal i 0
                                              then failwith "Impossible to lower zero" 
                                              else (name, i-n)
let eqVar ((_ , i) : var) ((_ , j) : var) : bool = Int.equal i j
                                     
let rec subst (x : var) (s : term) (t : term) : term =
  match t with
  | Fun (o , tl) -> Fun (o , List.map ~f:(subst x s) tl)
  | App (f , tl) -> App (subst x s f, List.map ~f:(subst x s) tl)
  | BVar bv -> if eqVar bv x
               then s 
               else BVar (down bv 1)
  | FVar fv -> FVar fv
  | Lam (i, t) -> Lam (i , subst (up x 1) s t)
        
let rec openTerm (name : id) (t : term) : term = subst (name , 0) (FVar (fresh name)) t

let closeTerm (v : var) (t : term) : term =
  let rec closeTerm_aux (v : var) (bv : var) (t : term) : term =
    match t with 
    | Fun (o , tl) -> Fun (o , List.map ~f:(closeTerm_aux v bv) tl)
    | App (f , tl) -> App (closeTerm_aux v bv f, List.map ~f:(closeTerm_aux v bv) tl)
    | BVar bv -> BVar (up bv 1)
    | FVar fv -> if eqVar fv v
                 then BVar bv
                 else FVar fv
    | Lam (i, t) -> Lam (i , closeTerm_aux v (up bv 1) t)    
  in closeTerm_aux v (fst v , 0) t
       
let rec apart (x : var) (t : term) : bool =
  match t with
  | Fun (o , tl) -> List.for_all ~f:(apart x) tl
  | App (f , tl) -> apart x f && List.for_all ~f:(apart x) tl
  | BVar bv -> true
  | FVar fv -> if eqVar fv x
               then false
               else true
  | Lam (_ , s) -> apart x s
                       
let rec foldMaybe b f l =
  match l with
  | [] -> Some b 
  | x :: xs ->
     (match f x b with
        None -> None
      | Some y -> foldMaybe y f xs)

let rec mapMaybe f l = Option.value_map ~f:f ~default:None l
     
let uncurry f (a,b) = f a b

let rec lookup i rho =
  List.find ~f:(fun (x , t) -> eqVar x i) rho
                 
let rec unify (x : term) (y : term) (rho : rho) : rho option =
  match x with
    Fun (o1 , tl1) ->
      (match y with
         Fun (o2 , tl2) ->
         Option.find_map ~f:(foldMaybe rho (uncurry unify)) (List.zip tl1 tl2)
       | App (t , tl) -> None (* normalise??? *)
       | BVar j -> failwith "Higher order unification is unimplemented"
       | FVar j -> bind j x rho
       | Lam _ -> None)
  | App (t1 , tl1) -> 
     (match y with
      | Fun (o2 , tl2) -> None
      | App (t2 , tl2) ->
         (match unify t1 t2 rho with
            None -> None
          | Some rho' -> Option.find_map ~f:(foldMaybe rho' (uncurry unify)) (List.zip tl1 tl2))
      | BVar j -> failwith "Higher order unification is unimplemented"
      | FVar j -> bind j (App (t1 , tl1)) rho
      | Lam _ -> None)
  | BVar i -> failwith "Higher order unification is unimplemented"
  | FVar i -> bind i y rho
  | Lam (q , t) -> failwith "Higher order unification is unimplemented"
and bind (i : var) t rho : rho option =
  match lookup i rho with
  | None -> Some ((i , t)::rho)
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
  | T () , T () -> true
  | Int () , Int () -> true
  | Arr (d1 , r1) , Arr (d2 , r2) -> tyeq d1 d2 && tyeq r1 r2
  | Bool () , Bool () -> true
  | Times (a1 , b1) , Times (a2 , b2) -> true
  | Plus (a1 , b1) , Plus (a2 , b2) -> true
  | _ -> false

let rec checkTermType (s : term) (ty : ty) (ctx : typedefCtx) : bool =
  match s with
  | Fun _ -> (??)
  | App (_,_) -> (??)
  | BVar _ -> (??)
  | FVar _ -> (??)
  | Lam (_,_) -> (??)                   
and inferTermType (s : term) : ty option =
  match s with
  | Fun _ -> (??)
  | App (_,_) -> (??)
  | BVar _ -> (??)
  | FVar _ -> (??)
  | Lam (_,_) -> (??)
  		         
let rec opType op tl gamma objGamma =
  if String.equal op "app"
  then let tylisto = mapMaybe (fun t -> infer t gamma objGamma) tl in
       match tylisto with
       | None -> None
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
     | None -> None
     | Some (tylist, ty) -> oo)
  | Var i -> oo
  | Lam (i , t) -> oo
and checkObj x ty gamma objGamma =
  match x with
  | Op (o , tl) -> true
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
