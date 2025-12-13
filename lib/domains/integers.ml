(* Rationals *)
(* Author: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) Integers(Integer : INTEGER) : INTEGERS =
struct

  open Integer

  (* GEN BEGIN TAG OUTSIDE LET *) val zero = fromInt 0 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val one = fromInt 1 (* GEN END TAG OUTSIDE LET *)

  fun solve_gcd (m, n) =
        let
          fun solve' (m, n) =
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val q = quot (m, n) (* GEN END TAG OUTSIDE LET *)
                  (* GEN BEGIN TAG OUTSIDE LET *) val r = rem (m, n) (* GEN END TAG OUTSIDE LET *)
                in
                  if (r = zero) then (zero, one)
                  else
                    let
                      (* GEN BEGIN TAG OUTSIDE LET *) val (x, y) = solve' (n, r) (* GEN END TAG OUTSIDE LET *)
                    in
                      (y, x - q*y)
                    end
                end
          (* GEN BEGIN TAG OUTSIDE LET *) val am = abs m (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val an = abs n (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val sm = fromInt (sign m) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val sn = fromInt (sign n) (* GEN END TAG OUTSIDE LET *)
        in
          if (am > an)
          then ((* GEN BEGIN FUNCTION EXPRESSION *) fn (x, y) => (sm*x, sn*y) (* GEN END FUNCTION EXPRESSION *)) (solve' (am, an))
          else ((* GEN BEGIN FUNCTION EXPRESSION *) fn (x, y) => (sm*y, sn*x) (* GEN END FUNCTION EXPRESSION *)) (solve' (an, am))
        end

  fun gcd (m, n) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (x, y) = solve_gcd (m, n) (* GEN END TAG OUTSIDE LET *)
        in
          m*x + n*y
        end

  fun lcm (m, n) = quot (m*n, gcd (m, n))

  fun fromString (str) =
        let
          fun (* GEN BEGIN FUN FIRST *) check (chars as (c :: chars')) =
                if (c = #"~")
                then (List.all Char.isDigit chars')
                else (List.all Char.isDigit chars) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) check nil =
                false (* GEN END FUN BRANCH *)
        in
          if check (String.explode str)
          then Integer.fromString str
          else NONE
        end

end (* GEN END FUNCTOR DECL *);  (* structure Integers *)
