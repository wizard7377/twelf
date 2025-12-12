(* Compatibility shim from Basis-current Vector to Basis-97 Vector *)
(* Author: Christopher Richards *)

structure CompatVector97 :> COMPAT_VECTOR =
struct
  (* GEN BEGIN TAG INSIDE LET *) fun appi f vec = Vector.appi f (vec, 0, NONE) (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) fun mapi f vec = Vector.mapi f (vec, 0, NONE) (* GEN END TAG INSIDE LET *)
end;
