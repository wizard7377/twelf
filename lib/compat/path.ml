(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT_PATH = sig
  val mkAbsolute : < path : string ; relativeTo : string > -> string
end
(* Compatibility shim from Basis-current OS.Path to Basis-97 OS.Path *)

(* Author: Christopher Richards *)

module CompatPath97 : COMPAT_PATH = struct
  let rec mkAbsolute { path; relativeTo } = OS.Path.mkAbsolute (path, relativeTo)
end
