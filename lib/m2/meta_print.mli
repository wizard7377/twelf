(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

module type METAPRINT =
sig
  module MetaSyn : METASYN

  val stateToString  : MetaSyn.state -> string
  val sgnToString    : MetaSyn.Sgn -> string
  val modeToString   : MetaSyn.mode -> string
  val conDecToString  : IntSyn.conDec -> string

end;; (* module type METAPRINT *)
