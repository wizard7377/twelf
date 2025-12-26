(** LargeInt module - SML Basis Library INTEGER signature for large integers *)

(* In OCaml, we use the built-in int type which is already quite large *)
(* For truly arbitrary precision, one would use Zarith or Num, but for *)
(* Twelf's purposes, native int should be sufficient *)

open Order

module type LARGE_INT = sig
  type int

  val toInt : int -> Stdlib.Int.t
  val fromInt : Stdlib.Int.t -> int
  val precision : int option
  val minInt : int option
  val maxInt : int option

  val ( ~- ) : int -> int
  val ( + ) : int * int -> int
  val ( - ) : int * int -> int
  val ( * ) : int * int -> int
  val div : int * int -> int
  val modulo : int * int -> int
  val quot : int * int -> int
  val rem : int * int -> int

  val compare : int * int -> order
  val ( < ) : int * int -> bool
  val ( <= ) : int * int -> bool
  val ( > ) : int * int -> bool
  val ( >= ) : int * int -> bool

  val abs : int -> int
  val min : int * int -> int
  val max : int * int -> int
  val sign : int -> int
  val sameSign : int * int -> bool

  val toString : int -> string
  val fromString : string -> int option
end

module LargeInt : LARGE_INT = struct
  type int = Stdlib.Int.t

  let toInt x = x
  let fromInt x = x
  let precision = Some Sys.int_size
  let minInt = Some min_int
  let maxInt = Some max_int

  let ( ~- ) x = -x
  let ( + ) (x, y) = x + y
  let ( - ) (x, y) = x - y
  let ( * ) (x, y) = x * y
  let div (x, y) = x / y
  let modulo (x, y) = x mod y
  let quot (x, y) = x / y
  let rem (x, y) = x mod y

  let compare (x, y) =
    if x < y then Less
    else if x > y then Greater
    else Equal

  let ( < ) (x, y) = x < y
  let ( <= ) (x, y) = x <= y
  let ( > ) (x, y) = x > y
  let ( >= ) (x, y) = x >= y

  let abs x = if x < 0 then -x else x
  let min (x, y) = if x < y then x else y
  let max (x, y) = if x > y then x else y
  let sign x = if x < 0 then -1 else if x = 0 then 0 else 1
  let sameSign (x, y) =
    (x < 0 && y < 0) || (x = 0 && y = 0) || (x > 0 && y > 0)

  let toString = string_of_int
  let fromString s = try Some (int_of_string s) with Failure _ -> None
end
