(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

signature METAPRINT =
sig
  structure MetaSyn : METASYN

  val stateToString  : MetaSyn.state -> string
  val sgnToString    : MetaSyn.sgn -> string
  val modeToString   : MetaSyn.mode -> string
  val conDecToString  : IntSyn.con_dec -> string

end; (* signature METAPRINT *)
