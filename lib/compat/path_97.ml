(* Compatibility shim from Basis-current OS.Path to Basis-97 OS.Path *)
(* Author: Christopher Richards *)

structure CompatPath97 :> COMPAT_PATH =
struct
  (* GEN BEGIN TAG INSIDE LET *) fun mkAbsolute {path=path, relativeTo=relativeTo} =
      OS.Path.mkAbsolute (path, relativeTo) (* GEN END TAG INSIDE LET *)
end;
