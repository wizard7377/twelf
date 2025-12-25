open Basis ;; 

module type MSG = sig
  val message : string -> unit
  val setMessageFunc : (string -> unit) -> unit
end

module Msg : MSG = struct
  let default s = print_string s
  let messageFunc = ref default
  let setMessageFunc f = messageFunc := f
  let message s = !messageFunc s
end
