(* Rationals *)
(* Author: Roberto Virga *)

let recctor Integers(Integer : INTEGER) : INTEGERS =
struct

  open Integer

  let zero = fromInt 0
  let one = fromInt 1

  fun solve_gcd (m, n) =
        let
          fun solve' (m, n) =
                let
                  let q = quot (m, n)
                  let r = rem (m, n)
                in
                  if (r = zero) then (zero, one)
                  else
                    let
                      let (x, y) = solve' (n, r)
                    in
                      (y, x - q*y)
                    end
                end
          let am = abs m
          let an = abs n
          let sm = fromInt (sign m)
          let sn = fromInt (sign n)
        in
          if (am > an)
          then (fn (x, y) => (sm*x, sn*y)) (solve' (am, an))
          else (fn (x, y) => (sm*y, sn*x)) (solve' (an, am))
        end

  fun gcd (m, n) =
        let
          let (x, y) = solve_gcd (m, n)
        in
          m*x + n*y
        end

  fun lcm (m, n) = quot (m*n, gcd (m, n))

  fun fromString (str) =
        let
          fun check (chars as (c :: chars')) =
                if (c = #"~")
                then (List.all Char.isDigit chars')
                else (List.all Char.isDigit chars)
            | check nil =
                false
        in
          if check (String.explode str)
          then Integer.fromString str
          else NONE
        end

end;  (* module Integers *)
