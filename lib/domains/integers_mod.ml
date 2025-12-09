(* Integers Modulo a Prime Number *)
(* Author: Roberto Virga *)

module IntegersMod (let p : int) : FIELD =
struct

  let name = "integer" ^ (Int.toString p)

  type number = int

  let rec normalize (n) = n mod p

  let zero = 0
  let one  = 1

  exception Div

  let rec op~ (n) = Int.-(p, n)

  let rec op+ (m, n) = normalize (Int.+(m, n))

  let rec op- (m, n) = normalize (Int.-(m, n))

  let rec op* (m, n) = normalize (Int.*(m, n))

  let rec inverse = function (0) -> raise Div
    | (n) -> 
        let
          (* alternative: compute n^(p-2) *)
          let rec inverse' i =
                if (normalize (Int.*(n, i)) = 1) then i
                else inverse' (Int.+(i, 1))
        in
          inverse' 1
        end

  let rec fromInt (n) = normalize (n)

  let rec fromString (str) =
        let
          let check = (List.all Char.isDigit)
        in
          if check (String.explode str) then
            (case (Int.fromString (str))
               of SOME (n) =>
                    if (n < p) then SOME (n)
                    else NONE
                | NONE => NONE)
          else NONE
        end

  let toString = Int.toString

end;; (* functor IntegersMod *)
