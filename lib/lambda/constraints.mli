(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)

module type CONSTRAINTS =
sig

  (*! module IntSyn : INTSYN !*)

   exception Error of IntSyn.cnstr list

   val simplify : IntSyn.cnstr list -> IntSyn.cnstr list
   val warnConstraints : string list -> unit

end;  (* module type CONSTRAINTS *)
