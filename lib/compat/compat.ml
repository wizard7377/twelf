(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT = sig
  val inputLine97 : TextIO.instream -> string

  module Array : Array.COMPAT_ARRAY
  module Vector : Vector.COMPAT_VECTOR

  module OS : sig
    module Path : Path.COMPAT_PATH
  end

  module Substring : Substring.COMPAT_SUBSTRING
  module TextIO : Text_io.COMPAT_TEXT_IO
  module Timer : Timer.COMPAT_TIMER
  module SocketIO : Socket.COMPAT_SOCKET_IO
end
(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module Compat
    (Array : Array.COMPAT_ARRAY)
    (Vector : Vector.COMPAT_VECTOR)
    (Path : Path.COMPAT_PATH)
    (Substring : Substring.COMPAT_SUBSTRING)
    (TextIO : Text_io.COMPAT_TEXT_IO)
    (Timer : Timer.COMPAT_TIMER)
    (SocketIO : Socket.COMPAT_SOCKET_IO) : COMPAT = struct
  module Array = Array
  module Vector = Vector

  module OS = struct
    module Path = Path
  end

  module Substring = Substring
  module TextIO = TextIO
  module Timer = Timer
  module SocketIO = SocketIO

  let rec inputLine97 instream = getOpt (TextIO.inputLine instream, "")
end
