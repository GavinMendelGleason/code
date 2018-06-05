
(* 

What do we need to have an appropriate prolog which is usable from scratch as a DB and can grow into a language? 

1. Types: We need to be able to inductively describe typing information for terms. 

2. Determinacy: We need to detect determinacy and coverage - some of this can be done using types. 

3. Storage: We need a backing store for predicates labelled as mutable and an indexing strategy.

4. Higher-Order: I want to be able to store and use predicates but *not* to match on them. We should be able to refuse unification of higher order predicates - or perhaps with some extension, to restrict higher order unification to some fragment. 

5. URI based: We want terms to be based on URIs, dereferencable and self-describing. Documentation should be as complete as it can be, with meta-data which can be added as needed and code treated as within a database itself. 

6. Mode management: Ability to write particular modes, mode analysis, and possibly a functional language for specific modes.

Nice to haves: 

1. Distributed predicates / calls? 


*) 

module type Variable = sig
  type t
  val fresh : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
  val to_user_string : t -> string
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

module type Environment = sig
  type v
  type t
  type env = (v * t) list
  val bind : v -> t -> env option
end

module Exp = struct

                  
end
