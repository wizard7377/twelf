(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT_SUBSTRING = sig
  val full : string -> Substring.substring
end
(* Compatibility shim from Basis-current Substring to Basis-97 Substring *)

(* Author: Christopher Richards *)

module CompatSubstring97 : Compat.COMPAT_SUBSTRING = struct
  let full = Substring.all
end
