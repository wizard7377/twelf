(* Rationals *)
(* Author: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) Rationals (Integers : INTEGERS) : RATIONALS =
struct

  structure Integers = Integers

  (* GEN BEGIN TAG OUTSIDE LET *) val name = "rational" (* GEN END TAG OUTSIDE LET *)

  exception Div = Div

  local
    structure I = Integers

    datatype number =                          (* Rational number:              *)
      Fract of Int.int * I.int * I.int         (* q := Fract (sign, num, denom) *)

    (* GEN BEGIN TAG OUTSIDE LET *) val zero = Fract (0, I.fromInt(0), I.fromInt(1)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val one  = Fract (1, I.fromInt(1), I.fromInt(1)) (* GEN END TAG OUTSIDE LET *)

    exception Div

    fun (* GEN BEGIN FUN FIRST *) normalize (Fract (0, _, _)) = zero (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalize (Fract (s, n, d)) =
          let
            fun gcd (m, n) =
                  if (m = I.fromInt(0)) then n
                  else if (n = I.fromInt(0)) then m
                  else if I.>(m, n) then gcd (I.mod(m, n), n)
                  else gcd (m, I.mod(n, m))
            (* GEN BEGIN TAG OUTSIDE LET *) val g = gcd (n, d) (* GEN END TAG OUTSIDE LET *)
          in
            Fract (s, I.div(n, g), I.div(d, g))
          end (* GEN END FUN BRANCH *)

    fun op~ (Fract (s, n, d)) = (Fract (Int.~(s), n, d))

    fun op+ (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val n = I.+(I.*(I.*(I.fromInt(s1), n1), d2),
                        I.*(I.*(I.fromInt(s2), n2), d1)) (* GEN END TAG OUTSIDE LET *)
          in
            normalize (Fract (I.sign(n), I.abs(n), I.*(d1, d2)))
          end

    fun op- (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val n = I.-(I.*(I.*(I.fromInt(s1), n1), d2),
                        I.*(I.*(I.fromInt(s2), n2), d1)) (* GEN END TAG OUTSIDE LET *)
          in
            normalize (Fract (I.sign(n), I.abs(n), I.*(d1, d2)))
          end

    fun op* (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          normalize (Fract(Int.*(s1, s2), I.*(n1, n2), I.*(d1, d2)))

    fun (* GEN BEGIN FUN FIRST *) inverse (Fract (0, _, _)) = raise Div (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) inverse (Fract (s, n, d)) = (Fract (s, d, n)) (* GEN END FUN BRANCH *)

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
            fun (* GEN BEGIN FUN FIRST *) check_numerator (chars as (c :: chars')) =
                  if (c = #"~")
                  then (List.all Char.isDigit chars')
                  else (List.all Char.isDigit chars) (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) check_numerator nil =
                  false (* GEN END FUN BRANCH *)
            fun check_denominator (chars) =
                  (List.all Char.isDigit chars)
            (* GEN BEGIN TAG OUTSIDE LET *) val fields = (String.fields ((* GEN BEGIN FUNCTION EXPRESSION *) fn c => (c = #"/") (* GEN END FUNCTION EXPRESSION *)) str) (* GEN END TAG OUTSIDE LET *)
        in
          if (List.length fields = 1)
          then
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val numerator = List.nth (fields, 0) (* GEN END TAG OUTSIDE LET *)
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
              (* GEN BEGIN TAG OUTSIDE LET *) val numerator = List.nth (fields, 0) (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val denominator = List.nth (fields, 1) (* GEN END TAG OUTSIDE LET *)
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
            (* GEN BEGIN TAG OUTSIDE LET *) val nStr = I.toString (I.* (I.fromInt(s), n)) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val dStr = I.toString d (* GEN END TAG OUTSIDE LET *)
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

    (* GEN BEGIN TAG OUTSIDE LET *) val zero = zero (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val one = one (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val op~ = op~ (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val op+ = op+ (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val op- = op- (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val op* = op* (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val inverse = inverse (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val fromInt = fromInt (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val fromString = fromString (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val toString = toString (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val sign = sign (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val abs = abs (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val op> = op> (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val op< = op< (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val op>= = op>= (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val op<= = op<= (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val compare = compare (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val fromInteger = fromInteger (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val floor = floor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val ceiling = ceiling (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val numerator = numerator (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val denominator = denominator (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *);  (* structure Rationals *)
