(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature METAPRINT =
sig
  structure MetaSyn : METASYN

  val stateToString  : MetaSyn.state -> string
  val sgnToString    : MetaSyn.sgn -> string
  val modeToString   : MetaSyn.mode -> string
  val conDecToString  : IntSyn.con_dec -> string

end (* GEN END SIGNATURE DECLARATION *); (* signature METAPRINT *)
