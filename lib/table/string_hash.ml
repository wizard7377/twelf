(* String Hash Table *)
(* Author: Frank Pfenning *)

structure StringHash :> STRING_HASH =
struct
  (* GEN BEGIN TAG INSIDE LET *) fun stringHash (s) =
      (* sample 4 characters from string *)
      let
  	fun num (i) = Char.ord (String.sub (s,i)) mod 128
  	val n = String.size (s)
      in
  	if n = 0 then 0
  	else let
  	       val a = n-1
  	       val b = n div 2
  	       val c = b div 2
  	       val d = b + c
  	     in
  	       num(a)+128*(num(b)+128*(num(c)+128*num(d)))
  	     end
      end (* GEN END TAG INSIDE LET *)
end;  (* structure StringHash *)
