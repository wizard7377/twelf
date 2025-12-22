(* Compatibility shim to cope with Standard Basis version skew *)

(* Author: Christopher Richards *)

module type COMPAT = sig
  val inputLine97 : TextIO.instream -> string

  module Array : COMPAT_ARRAY
  module Vector : COMPAT_VECTOR

  module OS : sig
    module Path : COMPAT_PATH
  end

  module Substring : COMPAT_SUBSTRING
  module TextIO : COMPAT_TEXT_IO
  module Timer : COMPAT_TIMER
  module SocketIO : COMPAT_SOCKET_IO
end
