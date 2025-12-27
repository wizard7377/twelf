(** Math module - SML Basis Library MATH signature *)

module type MATH = sig
  type real = float

  val pi : real
  val e : real

  val sqrt : real -> real
  val sin : real -> real
  val cos : real -> real
  val tan : real -> real
  val asin : real -> real
  val acos : real -> real
  val atan : real -> real
  val atan2 : real -> real -> real

  val exp : real -> real
  val pow : real -> real -> real
  val ln : real -> real
  val log10 : real -> real

  val sinh : real -> real
  val cosh : real -> real
  val tanh : real -> real
end

module Math : MATH = struct
  type real = float

  let pi = 4.0 *. atan 1.0
  let e = exp 1.0

  let sqrt = sqrt
  let sin = sin
  let cos = cos
  let tan = tan
  let asin = asin
  let acos = acos
  let atan = atan
  let atan2 y x = atan2 y x

  let exp = exp
  let pow x y = x ** y
  let ln = log
  let log10 = log10

  let sinh = sinh
  let cosh = cosh
  let tanh = tanh
end
