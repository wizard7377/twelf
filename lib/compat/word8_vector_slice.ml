(* Compatibility shim from Basis-02 Word8VectorSlice to Basis-97 Word8Vector *)
(* Author: Christopher Richards *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MONO_VECTOR_SLICE =
sig
  type slice
  type vector
  val slice : vector * int * int option -> slice
  val vector : slice -> vector
  val full : vector -> slice
end (* GEN END SIGNATURE DECLARATION *);

structure Word8VectorSlice :> MONO_VECTOR_SLICE
			       where type vector = Word8Vector.vector =
struct
  type vector = Word8Vector.vector
  type slice = Word8Vector.vector * int * int option
  fun slice s = s
  (* GEN BEGIN TAG OUTSIDE LET *) val vector = Word8Vector.extract (* GEN END TAG OUTSIDE LET *)
  fun full v = (v, 0, NONE)
end;

(* GEN BEGIN SIGNATURE DECLARATION *) signature COMPAT_WORD8_VECTOR_SLICE =
sig
  val full : Word8Vector.vector -> Word8VectorSlice.slice
end (* GEN END SIGNATURE DECLARATION *);

structure Word8VectorSlice97 :> COMPAT_WORD8_VECTOR_SLICE =
struct
  type vector = Word8Vector.vector
  type slice = Word8VectorSlice.slice
  (* GEN BEGIN TAG OUTSIDE LET *) val full = Word8VectorSlice.full (* GEN END TAG OUTSIDE LET *)
end;
