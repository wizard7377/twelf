(* Compatibility shim from Basis-current ArraySlice to Basis-97 Array *)
(* Author: Christopher Richards *)

structure ArraySlice :> ARRAY_SLICE =
struct
  type 'a slice = 'a Array.array * int * int option
  fun slice s = s
  (* GEN BEGIN TAG OUTSIDE LET *) val appi = Array.appi (* GEN END TAG OUTSIDE LET *)
end;
