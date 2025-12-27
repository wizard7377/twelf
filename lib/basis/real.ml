(** Real module - SML Basis Library REAL signature *)

open Order
module StringCvt = StringCvt.StringCvt

module type REAL = sig
  type real = float

  val radix : int
  val precision : int
  val maxFinite : real
  val minPos : real
  val minNormalPos : real
  val posInf : real
  val negInf : real
  val ( + ) : real -> real -> real
  val ( - ) : real -> real -> real
  val ( * ) : real -> real -> real
  val ( / ) : real -> real -> real
  val rem : real -> real -> real
  val ( ~- ) : real -> real
  val abs : real -> real
  val min : real -> real -> real
  val max : real -> real -> real
  val sign : real -> int
  val signBit : real -> bool
  val sameSign : real -> real -> bool
  val copySign : real -> real -> real
  val compare : real -> real -> order
  val compareReal : real -> real -> order
  val ( < ) : real -> real -> bool
  val ( <= ) : real -> real -> bool
  val ( > ) : real -> real -> bool
  val ( >= ) : real -> real -> bool
  val equal : real -> real -> bool
  val notEqual : real -> real -> bool
  val unordered : real -> real -> bool
  val isFinite : real -> bool
  val isNan : real -> bool
  val isNormal : real -> bool
  val toInt : real -> int
  val fromInt : int -> real
  val toString : real -> string
  val fromString : string -> real option
  val fmt : StringCvt.realfmt -> real -> string
end

module Real : REAL = struct
  type real = float

  let radix = 2
  let precision = 53 (* IEEE 754 double precision *)
  let maxFinite = max_float
  let minPos = min_float
  let minNormalPos = min_float
  let posInf = infinity
  let negInf = neg_infinity
  let ( + ) x y = x +. y
  let ( - ) x y = x -. y
  let ( * ) x y = x *. y
  let ( / ) x y = x /. y
  let rem x y = mod_float x y
  let ( ~- ) x = -.x
  let abs = abs_float
  let min x y = if x < y then x else y
  let max x y = if x > y then x else y
  let sign x = if x < 0.0 then -1 else if x > 0.0 then 1 else 0
  let signBit x = x < 0.0 || (x = 0.0 && 1.0 /. x < 0.0)
  let sameSign x y = (x < 0.0 && y < 0.0) || (x >= 0.0 && y >= 0.0)
  let copySign x y = if signBit y then -.abs x else abs x
  let compare x y = if x < y then Less else if x > y then Greater else Equal
  let compareReal = compare
  let ( < ) x y = x < y
  let ( <= ) x y = x <= y
  let ( > ) x y = x > y
  let ( >= ) x y = x >= y
  let equal x y = x = y
  let notEqual x y = x <> y
  let unordered x y = classify_float x = classify_float y
  let isFinite x = classify_float x <> FP_infinite && classify_float x <> FP_nan
  let isNan x = classify_float x = FP_nan
  let isNormal x = classify_float x = FP_normal
  let toInt x = int_of_float x
  let fromInt x = float_of_int x
  let toString = string_of_float
  let fromString s = try Some (float_of_string s) with Failure _ -> None

  let fmt realfmt x =
    match realfmt with
    | StringCvt.SCI None -> Printf.sprintf "%e" x
    | StringCvt.SCI (Some n) -> Printf.sprintf "%.*e" n x
    | StringCvt.FIX None -> Printf.sprintf "%f" x
    | StringCvt.FIX (Some n) -> Printf.sprintf "%.*f" n x
    | StringCvt.GEN None -> Printf.sprintf "%g" x
    | StringCvt.GEN (Some n) -> Printf.sprintf "%.*g" n x
    | StringCvt.EXACT -> Printf.sprintf "%h" x
end
