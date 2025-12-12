(* Qed *)
(* Author: Carsten Schuermann *)

signature QED =
sig
  structure MetaSyn : METASYN

  exception Error of string

  val subgoal : MetaSyn.state -> bool
end;  (* signature QED *)
