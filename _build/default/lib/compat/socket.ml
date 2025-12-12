(* Compatibility shim from Basis-current Socket to Basis-97 Socket *)
(* Author: Christopher Richards *)

structure CompatSocketIO :> COMPAT_SOCKET_IO =
struct
(* GEN BEGIN TAG INSIDE LET *) fun sendVec (sock, vs) = Socket.sendVec (sock, Word8VectorSlice.full vs) (* GEN END TAG INSIDE LET *)
end
