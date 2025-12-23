(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT_ARRAY = sig
  val appi : (int * 'a -> unit) -> 'a Array.array -> unit
end
(* Compatibility shim from Basis-current Array to Basis-97 Array *)

(* Author: Christopher Richards *)

module CompatArray97 : Compat.COMPAT_ARRAY = struct
  let rec appi f arr = Array.appi f (arr, 0, None)
end
