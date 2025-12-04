(* Qed *)
(* Author: Carsten Schuermann *)

module type QED =
sig
  module MetaSyn : METASYN

  exception Error of string

  val subgoal : MetaSyn.state -> bool
end;  (* module type QED *)
