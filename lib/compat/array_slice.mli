(* Compatibility shim to cope with Standard Basis version skew *)


(* Author: Christopher Richards *)


module type ARRAY_SLICE = sig
  type 'a slice
  val slice : 'a Array.array * int * int option -> 'a slice
  val appi : (int * 'a -> unit) -> 'a slice -> unit

end

