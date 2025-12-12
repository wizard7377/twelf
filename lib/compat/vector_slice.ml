(* Compatibility shim from Basis-current VectorSlice to Basis-97 Vector *)
(* Author: Christopher Richards *)

structure VectorSlice :> VECTOR_SLICE =
struct
  type 'a slice = 'a Vector.vector * int * int option
  (* GEN BEGIN TAG INSIDE LET *) fun slice s = s (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val appi = Vector.appi (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val mapi = Vector.mapi (* GEN END TAG INSIDE LET *)
end;
