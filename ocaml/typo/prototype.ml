
open Base

let (>>=) = Result.(>>=)
let return = Result.return
let (>>=*) = Option.(>>=)

let uncurry f (a,b) = f a b
let curry f a b = f (a,b)
       
type id = string
type var = string * int

let eqId i j = String.equal i j

(* inductively defined types *)
type inductiveName = id
type inductiveTypeParameters = id list
type inductiveType = inductiveName * inductiveTypeParameters

type ty =
  | TyVar of id
  | Ind of inductiveType
  | Arr of ty * ty
  | T of unit
  | Int of unit
  | Bool of unit
  | Times of ty * ty
  | Plus of ty * ty

                   
let rec eqTy s t =
  match s , t with
  | TyVar id1 , TyVar id2 -> eqId id1 id2
  | T () , T () -> true
  | Int () , Int () -> true
  | Arr (d1 , r1) , Arr (d2 , r2) -> eqTy d1 d2 && eqTy r1 r2
  | Bool () , Bool () -> true
  | Times (a1 , b1) , Times (a2 , b2) -> true
  | Plus (a1 , b1) , Plus (a2 , b2) -> true
  | Ind (i1 , il1) , Ind (i2 , il2) -> eqId i1 i2 && Option.value_map (List.zip il1 il2) ~default:false ~f:(List.for_all ~f:(uncurry eqId)) 
  | _ -> false

(* constructors of inductive type *) 
type constructor = (id * ty list)
(* inductive type definition *)                             
type ind = inductiveType * constructor list

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
let down ((name , i) : var) (n : int) : var =
  if Int.equal i 0
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
        
let rec openTerm (name : id) (t : term) : (term * var) =
  let fv = fresh name
  in (subst (name , 0) (FVar fv) t, fv)

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

let rec everyOk l : bool = match l with
  | [] -> true
  | (x :: xs) ->
     (match x with
      | Error _ -> false
      | Ok _ -> everyOk xs)
                                        
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
type ctx = (var * ty) list

let rec lookupPredicateType i n objGamma =
  List.find ~f:(fun (j, tylist, ty) -> eqId i j && n = List.length tylist) objGamma 
       
let lookupTermType i gamma =
  List.find ~f:(fun (x , ty) -> eqId i x) gamma 

       
type typeError =
  | NoConstructor of id
  | BadConstructorArguments of typeError list
  | WrongNumberOfArgumentsToConstructor of term list * ty list 
  | ApplicationOfNonFunctionType of term * ty
  | FreeVariableWithNoType of var * ctx
  | FreeVariableWithWrongType of var * ty * ty
  | LambdaNotFunction of term * ty
  | TypesNotUnifiable of ty * ty
  | DifferentInductives of id * id list * id * id list
  | VariableLost of id * ctx

let lookupDefinition o (ctx : typedefCtx) : constructor option =
  List.find_map ctx ~f:(fun (it , constr) ->
                          List.find ~f:(fun (c , tyl') -> eqId o c) constr)

let lookupIndType o (ctx : typedefCtx) : inductiveType option =
  Option.value_map ~default:None ~f:(fun (it , _) -> Some it)
                   (List.find ctx ~f:(fun (x , constr) ->
                                List.exists ~f:(fun (c , tyl') -> eqId o c) constr))
                

let rec eval (obj : obj) ctx db =
  match obj with
  | Op t -> (??)
  | And _ -> (??)
  | Or _ -> (??)
  | Not _ -> (??)
                   
let failures lst = List.fold lst ~init:[] ~f:(fun r x -> match x with | Ok x -> r | Error e -> e :: r)

(* 
let rec unifyType (tya : ty) (tyb : ty) ctx : ((ctx * ty) , typeError) Result.t =
  match tya, tyb with
  | Ind (i, tyla), Ind (j, tylb) ->
     if eqId i j
     then let ctxee = List.fold2 tyla tylb ~init:(Ok ctx)
                               ~f:(fun r ida idb ->
                                 r >>= (fun ctx ->
                                 (bind ida idb ctx) >>= (fun ctx' ->
                                 return ctx')))
          in match ctxee with
             | Unequal_lengths -> Error (DifferentInductives (i,tyla,j,tylb))
             | Ok ctxe -> ??
     else Error (DifferentInductives (i,tyla,j,tylb))
  | Arr (_,_), Arr (_,_) ->     ??                                   
  | T () , T () -> Ok (ctx, T ())
  | Int () , Int () -> Ok (ctx, Int ())
  | Bool () , Bool () -> Ok (ctx, Bool ())
  | Times (_,_) , Times (_,_) -> (??)
  | Plus (_,_) , Plus (_,_) -> ??
  | TyVar _, TyVar _ -> ??
  | TyVar _, _ -> ??
  | _, TyVar _ -> ??
  | _ , _ -> Error (TypesNotUnifiable (tya,tyb))
and bind ida idb ctx = ??
                         
(* Inverts the meaning of option *)
let rec checkFunType (fty : ty) (tylst : ty list) : (unit , typeError) Result.t =
  ??
and applyFunType (fty : ty) (tylst : ty list) : (ty , typeError) Result.t =
  ??
and checkTermType (s : term) (ty : ty) gamma (ctx : typedefCtx) : (unit , typeError) Result.t =
  match s with
  | Fun (o , tl) ->
     Result.of_option (lookupDefinition o ctx)
               (NoConstructor o) >>= (fun (_ , tyl) ->
     Result.of_option (List.zip tl tyl)
               (WrongNumberOfArgumentsToConstructor (tl , tyl)) >>= (fun lst ->
     let errlist = failures (List.map lst (fun (t,ty) -> checkTermType t ty gamma ctx))
     in match errlist with
        | [] -> Ok ()
        | _ -> Error (BadConstructorArguments errlist)))
  | App (f , tl) ->
     let ftye = inferTermType f gamma ctx in
     (* Monadic error fold of type inference over arguments *)
     let xtyle = List.fold tl ~init:(Ok [])
                           ~f:(fun r t ->
                             match r with
                             | Error e -> Error e
                             | Ok tyl -> 
                                match inferTermType t gamma ctx with
                                | Ok ty -> Ok (ty :: tyl)
                                | Error e -> Error e)
     in ftye >>= (fun fty ->
        xtyle >>= (fun xtyl ->
        checkFunType fty xtyl))
  | BVar _ -> failwith "Should not encounter bound var in type-checking 'checkTermType'"
  | FVar fv ->
     (match lookup fv gamma with
      | None -> Error (FreeVariableWithNoType (fv , gamma))
      | Some (_,ty') -> if eqTy ty ty'
                        then Ok ()
                        else Error (FreeVariableWithWrongType (fv , ty , ty')))
  | Lam (x,t) ->
     (match ty with
      | Arr (tyx, tyy) ->
         let (ot, v) = openTerm x t
         in checkTermType ot tyy ((v, tyx) :: gamma) ctx
      | _ -> Error (LambdaNotFunction (s , ty)))                   
and inferTermType (s : term) gamma ctx : (ty , typeError) Result.t =
  match s with
  | Fun (i, tl) ->
     Result.of_option (lookupDefinition i ctx) (NoConstructor i) >>= (fun (i, tyl) ->
     Result.of_option (List.zip tl tyl)
               (WrongNumberOfArgumentsToConstructor (tl , tyl)) >>= (fun lst ->
     let errlist = failures (List.map lst (fun (t,ty) -> checkTermType t ty gamma ctx))
     in match errlist with
        | [] -> Result.of_option (lookupIndType i ctx >>=* (fun x -> 
                                  Some (Ind x)))
                                 (NoConstructor i)
        | _ -> Error (BadConstructorArguments errlist)))
  | App (f , x) ->
     let ftye = inferTermType f gamma ctx in
     (* Monadic error fold of type inference over arguments *)
     let xtyle = List.fold tl ~init:(Ok [])
                           ~f:(fun r t ->
                             match r with
                             | Error e -> Error e
                             | Ok tyl -> 
                                match inferTermType t gamma ctx with
                                | Ok ty -> Ok (ty :: tyl)
                                | Error e -> Error e)
     in ftye >>= (fun fty ->
        xtyle >>= (fun xtyl ->
        applyFunType fty xtyl))
  | BVar _ -> failwith "Should not encounter bound var in type-checking 'checkTermType'"
  | FVar fv ->
     (match lookup fv gamma with
      | None -> Error (FreeVariableWithNoType (fv , gamma))
      | Some (_,ty') -> Ok ty')
  | Lam (x,t) ->
     let (ot,v) = openTerm x t in
     let alpha = ?? 
     in inferTermType ot ((v, alpha) :: gamma) ctx >>= (fun (gamma, ty) ->
        Result.of_option (lookup v gamma) (VariableLost (x , gamma)) >>= (fun (v,ty) ->
        (match ty with
         | Arr (tyx, tyy) ->
            let (ot, v) = openTerm x t
            in ?? (* checkTermType ot tyy ((v, tyx) :: gamma) ctx *)
         | _ -> Error (LambdaNotFunction (s , ty)))))
       
(* 
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
                                     | Some (Arr (dom,range)) ->
                                        if tyeq dom vty
                                        then ??
                                        else None
                                     | Some _ -> None
                                   ) xtyl 
  else (* Assume 'op' is a constructor *)
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
 *)
                   
                                
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

 *)
