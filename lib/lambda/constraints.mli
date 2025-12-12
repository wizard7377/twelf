(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature CONSTRAINTS =
sig

  (*! structure IntSyn : INTSYN !*)

   exception Error of IntSyn.cnstr list

   val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
   val warnConstraints : string list -> unit

end (* GEN END SIGNATURE DECLARATION *);  (* signature CONSTRAINTS *)
