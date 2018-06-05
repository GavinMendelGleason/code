
module type Variable = sig
  type t
  val fresh : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
  val to_user_string : t -> string
end

module Var : Variable = struct
  type t = string * int
  let counter = ref 0
  let fresh n = (n, (counter := !counter + 1; !counter))
  let equal (_, id1) (_, id2) = id1 = id2
  let compare (_, id1) (_, id2) = id2 - id1
  let to_string (s, n) = s ^ "@" ^ string_of_int n
  let to_user_string (s, _) = s
end
                          
module type Operator = sig
  type t
  val arity : t -> int list
  val equal : t -> t -> bool
  val to_string : t -> string
end

module type Abt = sig
  module Variable : Variable
  module Operator : Operator

  type t

  type 'a view =
    | V of Variable.t
    | L of Variable.t * 'a
    | A of Operator.t * 'a list

  exception Malformed

  val into : t view -> t
  val out  : t -> t view

  val aequiv : t -> t -> bool
  val map : ('a -> 'b) -> ('a view -> 'b view)
end

(* 
module type Environment = sig
  where t = Variable.t
  type env : 
  
end*)

               


