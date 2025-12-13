(* Compatibility shim from Basis-current VectorSlice to Basis-97 Vector *)
(* Author: Christopher Richards *)

structure VectorSlice :> VECTOR_SLICE =
struct
  type 'a slice = 'a Vector.vector * int * int option
  fun slice s = s
  (* GEN BEGIN TAG OUTSIDE LET *) val appi = Vector.appi (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val mapi = Vector.mapi (* GEN END TAG OUTSIDE LET *)
end;
