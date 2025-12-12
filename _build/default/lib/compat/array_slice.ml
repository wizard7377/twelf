(* Compatibility shim from Basis-current ArraySlice to Basis-97 Array *)
(* Author: Christopher Richards *)

structure ArraySlice :> ARRAY_SLICE =
struct
  type 'a slice = 'a Array.array * int * int option
  (* GEN BEGIN TAG INSIDE LET *) fun slice s = s (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val appi = Array.appi (* GEN END TAG INSIDE LET *)
end;
