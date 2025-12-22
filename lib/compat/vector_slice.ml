(* Compatibility shim from Basis-current VectorSlice to Basis-97 Vector *)

(* Author: Christopher Richards *)

module VectorSlice : VECTOR_SLICE = struct
  type 'a slice = 'a Vector.vector * int * int option

  let rec slice s = s
  let appi = Vector.appi
  let mapi = Vector.mapi
end
