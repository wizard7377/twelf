(* Compatibility shim from Basis-current Socket to Basis-97 Socket *)
(* Author: Christopher Richards *)

structure CompatSocketIO97 :> COMPAT_SOCKET_IO =
struct
(* GEN BEGIN TAG INSIDE LET *) fun sendVec (sock, vs) = Socket.sendVec (sock, {buf = vs, i = 0, sz = NONE}) (* GEN END TAG INSIDE LET *)
end
