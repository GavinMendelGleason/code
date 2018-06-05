
module type AType = sig
  val test : unit -> unit
end

module type BType = sig
  include AType
  val test2 : unit -> unit
end

module A : AType = struct
  let test () = ()
end

module B : BType = struct
  open A
  let test = A.test
  let test2 () =
    print_string "foo";
    ()
end
                     
