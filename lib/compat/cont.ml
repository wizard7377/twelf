module type CONT = sig
  type 'a cont

  val callcc : ('a cont -> 'a) -> 'a
  val throw : 'a cont -> 'a -> 'b
  val isolate : ('a -> unit) -> 'a cont

  type 'a control_cont

  val capture : ('a control_cont -> 'a) -> 'a
  val escape : 'a control_cont -> 'a -> 'b
end

module Cont : CONT = struct
  type 'a cont = Capture of 'a

  let callcc = assert false
  let throw k v = assert false
  let isolate f = assert false

  type 'a control_cont = 'a cont

  let capture f = assert false
  let escape k v = assert false
end
