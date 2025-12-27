open Basis

(* Rational numbers *)

(* Author: Roberto Virga *)

module type RATIONALS = sig
  include Ordered_field.ORDERED_FIELD
  module Integers : Integers.INTEGERS

  (* Conversions between rationals and integers *)
  val fromInteger : Integers.t -> number
  val floor : number -> Integers.t
  val ceiling : number -> Integers.t

  (* Basic projections *)
  val numerator : number -> Integers.t
  val denominator : number -> Integers.t
end

(* signature RATIONALS *)
(* Rationals *)

(* Author: Roberto Virga *)

module Rationals (Integers : Integers.INTEGERS) : RATIONALS = struct
  module Integers = Integers

  let name = "rational"

  exception DivDiv

  module I = Integers

  type number = Fract of int * I.t * I.t
  (* q := Fract (sign, num, denom) *)

  let zero = Fract (0, I.fromInt 0, I.fromInt 1)
  let one = Fract (1, I.fromInt 1, I.fromInt 1)

  exception Div

  let rec normalize = function
    | Fract (0, _, _) -> zero
    | Fract (s, n, d) ->
        let rec gcd (m, n) =
          if m = I.fromInt 0 then n
          else if n = I.fromInt 0 then m
          else if I.( > ) m n then gcd (I.modulo m n, n)
          else gcd (m, I.modulo n m)
        in
        let g = gcd (n, d) in
        Fract (s, I.div n g, I.div d g)

  let ( ~- ) (Fract (s, n, d)) = Fract (Stdlib.( ~- ) s, n, d)

  let rec ( + ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
    let n =
      I.( + )
        (I.( * ) (I.( * ) (I.fromInt s1) n1) d2)
        (I.( * ) (I.( * ) (I.fromInt s2) n2) d1)
    in
    normalize (Fract (I.sign n, I.abs n, I.( * ) d1 d2))

  let rec ( - ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
    let n =
      I.( - )
        (I.( * ) (I.( * ) (I.fromInt s1) n1) d2)
        (I.( * ) (I.( * ) (I.fromInt s2) n2) d1)
    in
    normalize (Fract (I.sign n, I.abs n, I.( * ) d1 d2))

  let rec ( * ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
    normalize (Fract (Stdlib.( * ) s1 s2, I.( * ) n1 n2, I.( * ) d1 d2))

  let rec inverse = function
    | Fract (0, _, _) -> raise Div
    | Fract (s, n, d) -> Fract (s, d, n)

  let rec sign (Fract (s, n, d)) = s
  let rec numerator (Fract (s, n, d)) = n
  let rec denominator (Fract (s, n, d)) = d
  let rec abs (Fract (s, n, d)) = Fract (Int.abs s, n, d)

  let rec compare (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
    I.compare
      (I.( * ) (I.( * ) (I.fromInt s1) n1) d2)
      (I.( * ) (I.( * ) (I.fromInt s2) n2) d1)

  let rec ( > ) (q1, q2) = compare (q1, q2) = Greater
  let rec ( < ) (q1, q2) = compare (q1, q2) = Less
  let rec ( >= ) (q1, q2) = q1 = q2 || ( > ) (q1, q2)
  let rec ( <= ) (q1, q2) = q1 = q2 || ( < ) (q1, q2)
  let rec fromInt n = Fract (Integer.sign n, I.fromInt (Int.abs n), I.fromInt 1)

  let rec fromString str =
    let rec check_numerator = function
      | c :: chars' ->
          if c = '~' then List.all Char.isDigit chars'
          else List.all Char.isDigit (c :: chars')
      | [] -> false
    in
    let rec check_denominator chars = List.all Char.isDigit chars in
    let fields = String.fields (fun c -> c = '/') str in
    if List.length fields = 1 then
      let numerator = List.nth (fields, 0) in
      if check_numerator (String.explode numerator) then
        match I.fromString numerator with
        | Some n -> Some (Fract (I.sign n, I.abs n, I.fromInt 1))
        | _ -> None
      else None
    else if List.length fields = 2 then
      let numerator = List.nth (fields, 0) in
      let denominator = List.nth (fields, 1) in
      if
        check_numerator (String.explode numerator)
        && check_denominator (String.explode denominator)
      then
        match (I.fromString numerator, I.fromString denominator) with
        | Some n, Some d -> Some (normalize (Fract (I.sign n, I.abs n, d)))
        | _ -> None
      else None
    else None

  let rec toString (Fract (s, n, d)) =
    let nStr = I.toString (I.( * ) (I.fromInt s) n) in
    let dStr = I.toString d in
    if d = I.fromInt 1 then nStr else nStr ^ "/" ^ dStr

  let rec fromInteger n = Fract (I.sign n, I.abs n, I.fromInt 1)

  let rec floor (Fract (s, n, d) as q) =
    if (>=) (fromInt s, fromInt 0) then I.quot n d else Integers.( ~- ) (ceiling ~-q)

  and ceiling (Fract (s, n, d) as q) =
    if (>=) (fromInt s, fromInt 0) then I.(quot (n + (d - fromInt 1))) d
    else Integers.( ~- ) (floor ~-q)

  (* type number = Integers.t *)

  let zero = zero
  let one = one
  let ( ~- ) = ( ~- )
  let ( + ) = ( + )
  let ( - ) = ( - )
  let ( * ) = ( * )
  let inverse = inverse
  let fromInt = fromInt
  let fromString = fromString
  let toString = toString
  let sign = sign
  let abs = abs
  let ( > ) = ( > )
  let ( < ) = ( < )
  let ( >= ) = ( >= )
  let ( <= ) = ( <= )
  let compare = compare
  let fromInteger = fromInteger
  let floor = floor
  let ceiling = ceiling
  let numerator = numerator
  let denominator = denominator
end

(* structure Rationals *)
