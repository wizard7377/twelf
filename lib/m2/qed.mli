(* Qed *)
(* Author: Carsten Schuermann *)

module type QED =
sig
  module MetaSyn : METASYN

  exception Error of string

  val subgoal : MetaSyn.State -> bool
end;  (* module type QED *)
