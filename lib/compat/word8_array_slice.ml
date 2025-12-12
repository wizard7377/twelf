(* Compatibility shim from Basis-02 Word8ArraySlice to Basis-97 Word8Array *)
(* Author: Christopher Richards *)

structure Word8ArraySlice :> MONO_ARRAY_SLICE
			       where type array = Word8Array.array
			       where type vector = Word8Array.vector =
struct
  type array = Word8Array.array
  type slice = Word8Array.array * int * int option
  type vector = Word8Array.vector
  (* GEN BEGIN TAG INSIDE LET *) fun slice s = s (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val vector = Word8Array.extract (* GEN END TAG INSIDE LET *)
end;
