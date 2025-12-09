(* Rationals *)
(* Author: Roberto Virga *)

module Rationals (Integers : INTEGERS) : RATIONALS =
struct

  module Integers = Integers

  let name = "rational"

  exception Div = Div

  local
    module I = Integers

    type number =                          (* Rational number:              *)
      Fract of Int.int * I.int * I.int         (* q := Fract (sign, num, denom) *)

    let zero = Fract (0, I.fromInt(0), I.fromInt(1))
    let one  = Fract (1, I.fromInt(1), I.fromInt(1))

    exception Div

    let rec normalize = function (Fract (0, _, _)) -> zero
      | (Fract (s, n, d)) -> 
          let
            fun gcd (m, n) =
                  if (m = I.fromInt(0)) then n
                  else if (n = I.fromInt(0)) then m
                  else if I.>(m, n) then gcd (I.mod(m, n), n)
                  else gcd (m, I.mod(n, m))
            let g = gcd (n, d)
          in
            Fract (s, I.div(n, g), I.div(d, g))
          end

    fun op~ (Fract (s, n, d)) = (Fract (Int.~(s), n, d))

    fun op+ (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let
            let n = I.+(I.*(I.*(I.fromInt(s1), n1), d2),
                        I.*(I.*(I.fromInt(s2), n2), d1))
          in
            normalize (Fract (I.sign(n), I.abs(n), I.*(d1, d2)))
          end

    fun op- (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let
            let n = I.-(I.*(I.*(I.fromInt(s1), n1), d2),
                        I.*(I.*(I.fromInt(s2), n2), d1))
          in
            normalize (Fract (I.sign(n), I.abs(n), I.*(d1, d2)))
          end

    fun op* (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          normalize (Fract(Int.*(s1, s2), I.*(n1, n2), I.*(d1, d2)))

    let rec inverse = function (Fract (0, _, _)) -> raise Div
      | (Fract (s, n, d)) -> (Fract (s, d, n))

    fun sign (Fract (s, n, d)) = s

    fun numerator (Fract (s, n, d)) = n

    fun denominator (Fract (s, n, d)) = d

    fun abs (Fract (s, n, d)) = (Fract (Int.abs(s), n, d))

    fun compare (Fract (s1, n1, d1), Fract( s2, n2, d2)) =
          I.compare (I.*(I.*(I.fromInt(s1), n1), d2),
                     I.*(I.*(I.fromInt(s2), n2), d1))

    fun op> (q1, q2) = (compare (q1, q2) = GREATER)

    fun op< (q1, q2) = (compare (q1, q2) = LESS)

    fun op>= (q1, q2) = (q1 = q2) orelse (q1 > q2)

    fun op<= (q1, q2) = (q1 = q2) orelse (q1 < q2)

    fun fromInt (n) =
          (Fract (Int.sign (n),
                  I.fromInt (Int.abs (n)),
                  I.fromInt (1)))

    fun fromString (str) =
          let
            let rec check_numerator = function (chars as (c :: chars')) -> 
                  if (c = #"~")
                  then (List.all Char.isDigit chars')
                  else (List.all Char.isDigit chars)
              | nil -> 
                  false
            fun check_denominator (chars) =
                  (List.all Char.isDigit chars)
            let fields = (String.fields (fun c -> (c = #"/")) str)
        in
          if (List.length fields = 1)
          then
            let
              let numerator = List.nth (fields, 0)
            in
              if (check_numerator (String.explode (numerator)))
              then
                case (I.fromString (numerator))
                  of SOME (n) =>
                       SOME (Fract(I.sign(n),
                                   I.abs(n),
                                   I.fromInt(1)))
                   | _ =>
                       NONE
              else
                NONE
            end
          else if (List.length fields = 2)
          then
            let
              let numerator = List.nth (fields, 0)
              let denominator = List.nth (fields, 1)
            in
              if (check_numerator (String.explode (numerator)))
                andalso (check_denominator (String.explode (denominator)))
              then
                case (I.fromString (numerator), I.fromString (denominator))
                  of (SOME (n), SOME (d)) =>
                       SOME (normalize (Fract (I.sign(n), I.abs(n), d)))
                   | _ =>
                       NONE
              else
                NONE
            end
          else
            NONE
        end

    fun toString (Fract(s, n, d)) =
          let
            let nStr = I.toString (I.* (I.fromInt(s), n))
            let dStr = I.toString d
          in
            if (d = I.fromInt(1)) then nStr else (nStr ^ "/" ^ dStr)
          end

    fun fromInteger (n) =
          Fract (I.sign (n), I.abs (n), I.fromInt(1))

    fun floor (q as Fract (s, n, d)) =
          if Int.>=(s, 0)
          then I.quot (n, d)
          else Integers.~(ceiling (~ q))

    and ceiling (q as Fract (s, n, d)) =
          if Int.>=(s, 0)
          then I.quot (I.+ (n, I.- (d, I.fromInt(1))), d)
          else Integers.~(floor (~ q))

  in
    type number = number

    let zero = zero
    let one = one

    let op~ = op~
    let op+ = op+
    let op- = op-
    let op* = op*
    let inverse = inverse

    let fromInt = fromInt
    let fromString = fromString
    let toString = toString

    let sign = sign
    let abs = abs

    let op> = op>
    let op< = op<
    let op>= = op>=
    let op<= = op<=
    let compare = compare

    let fromInteger = fromInteger
    let floor = floor
    let ceiling = ceiling

    let numerator = numerator
    let denominator = denominator
  end
end;; (* module Rationals *)
