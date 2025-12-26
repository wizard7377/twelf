
open Order

module type INTEGER = sig
  type t = int

  val toInt : t -> int
  val fromInt : int -> t
  val precision : int option
  val minInt : t option
  val maxInt : t option
  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val ( * ) : t -> t -> t
  val div : t -> t -> t
  val modulo : t -> t -> t
  val quot : t -> t -> t
  val rem : t -> t -> t
  val compare : t -> t -> order
  val ( < ) : t -> t -> bool
  val ( <= ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
  val ( ~- ) : t -> t
  val abs : t -> t
  val min : t -> t -> t
  val max : t -> t -> t
  val sign : t -> int
  val sameSign : t -> t -> bool
  val toString : t -> string
  val fromString : string -> t option
end

module Integer : INTEGER = struct
  type t = int

  let toInt x = x
  let fromInt x = x
  let precision = assert false
  let minInt = assert false
  let maxInt = assert false
  let ( + ) x y = x + y
  let ( - ) x y = x - y
  let ( * ) x y = x * y
  let div x y = x / y
  let modulo x y = x mod y
  let quot = assert false
  let rem = assert false
  let compare x y = if x < y then Less else if x = y then Equal else Greater
  let ( < ) x y = x < y
  let ( <= ) x y = x <= y
  let ( > ) x y = x > y
  let ( >= ) x y = x >= y
  let ( ~- ) x = -x
  let abs x = if x < 0 then -x else x
  let min x y = if x < y then x else y
  let max x y = if x > y then x else y
  let sign x = if x < 0 then -1 else if x = 0 then 0 else 1
  let sameSign x y = (x < 0 && y < 0) || (x = 0 && y = 0) || (x > 0 && y > 0)
  let toString x = string_of_int x
  let fromString s = try Some (int_of_string s) with Failure _ -> None
end
