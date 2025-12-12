(* Initialization *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature INIT = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  val init : IntSyn.cid list -> MetaSyn.state list
end (* GEN END SIGNATURE DECLARATION *);  (* signature INIT *)
