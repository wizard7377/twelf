(* Compatibility shim to cope with Standard Basis version skew *)


(* Author: Christopher Richards *)


module type COMPAT_SOCKET_IO = sig
  val sendVec : ('a, Socket.active Socket.stream) Socket.sock * Word8Vector.vector -> int

end

