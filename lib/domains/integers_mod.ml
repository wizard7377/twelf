(* Integers Modulo a Prime Number *)
(* Author: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) IntegersMod (val p : int) :> FIELD =
struct

  (* GEN BEGIN TAG OUTSIDE LET *) val name = "integer" ^ (Int.toString p) (* GEN END TAG OUTSIDE LET *)

  type number = int

  fun normalize (n) = n mod p

  (* GEN BEGIN TAG OUTSIDE LET *) val zero = 0 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val one  = 1 (* GEN END TAG OUTSIDE LET *)

  exception Div

  fun op~ (n) = Int.-(p, n)

  fun op+ (m, n) = normalize (Int.+(m, n))

  fun op- (m, n) = normalize (Int.-(m, n))

  fun op* (m, n) = normalize (Int.*(m, n))

  fun (* GEN BEGIN FUN FIRST *) inverse (0) = raise Div (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) inverse (n) =
        let
          (* alternative: compute n^(p-2) *)
          fun inverse' i =
                if (normalize (Int.*(n, i)) = 1) then i
                else inverse' (Int.+(i, 1))
        in
          inverse' 1
        end (* GEN END FUN BRANCH *)

  fun fromInt (n) = normalize (n)

  fun fromString (str) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val check = (List.all Char.isDigit) (* GEN END TAG OUTSIDE LET *)
        in
          if check (String.explode str) then
            (case (Int.fromString (str))
               of SOME (n) =>
                    if (n < p) then SOME (n)
                    else NONE
                | NONE => NONE)
          else NONE
        end

  (* GEN BEGIN TAG OUTSIDE LET *) val toString = Int.toString (* GEN END TAG OUTSIDE LET *)

end (* GEN END FUNCTOR DECL *);  (* functor IntegersMod *)
