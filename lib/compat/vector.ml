(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT_VECTOR = sig
  val appi : (int * 'a -> unit) -> 'a Vector.vector -> unit
  val mapi : (int * 'a -> 'b) -> 'a Vector.vector -> 'b Vector.vector
end
(* Compatibility shim from Basis-current Vector to Basis-97 Vector *)

(* Author: Christopher Richards *)

module CompatVector97 : Compat.COMPAT_VECTOR = struct
  let rec appi f vec = Vector.appi f (vec, 0, None)
  let rec mapi f vec = Vector.mapi f (vec, 0, None)
end
