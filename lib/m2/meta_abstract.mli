(* Meta Abstraction *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature METAABSTRACT =
sig
  structure MetaSyn : METASYN

  exception Error of string

  val abstract : MetaSyn.state -> MetaSyn.state
end (* GEN END SIGNATURE DECLARATION *);  (* signature METAABSTRACT *)
