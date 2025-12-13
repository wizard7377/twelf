(* String Hash Table *)
(* Author: Frank Pfenning *)

structure StringHash :> STRING_HASH =
struct
  fun stringHash (s) =
      (* sample 4 characters from string *)
      let
  	fun num (i) = Char.ord (String.sub (s,i)) mod 128
  	(* GEN BEGIN TAG OUTSIDE LET *) val n = String.size (s) (* GEN END TAG OUTSIDE LET *)
      in
  	if n = 0 then 0
  	else let
  	       (* GEN BEGIN TAG OUTSIDE LET *) val a = n-1 (* GEN END TAG OUTSIDE LET *)
  	       (* GEN BEGIN TAG OUTSIDE LET *) val b = n div 2 (* GEN END TAG OUTSIDE LET *)
  	       (* GEN BEGIN TAG OUTSIDE LET *) val c = b div 2 (* GEN END TAG OUTSIDE LET *)
  	       (* GEN BEGIN TAG OUTSIDE LET *) val d = b + c (* GEN END TAG OUTSIDE LET *)
  	     in
  	       num(a)+128*(num(b)+128*(num(c)+128*num(d)))
  	     end
      end
end;  (* structure StringHash *)
