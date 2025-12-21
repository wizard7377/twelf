(* Compatibility shim from Basis-02 Word8ArraySlice to Basis-97 Word8Array *)

(* Author: Christopher Richards *)

module Word8ArraySlice :
  MONO_ARRAY_SLICE
    with type array = Word8Array.array
    with type vector = Word8Array.vector = struct
  type array = Word8Array.array
  type slice = Word8Array.array * int * int option
  type vector = Word8Array.vector

  let rec slice s = s
  let vector = Word8Array.extract
end
