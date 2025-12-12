(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature UNIQUE =
sig

  exception Error of string

  val checkUnique : (IntSyn.cid * ModeSyn.mode_spine) -> unit  (* raises Error(msg) *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature UNIQUE *)
