(* Qed *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature QED =
sig
  structure MetaSyn : METASYN

  exception Error of string

  val subgoal : MetaSyn.state -> bool
end (* GEN END SIGNATURE DECLARATION *);  (* signature QED *)
