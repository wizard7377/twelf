(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

module type METAPRINT =
sig
  module MetaSyn : METASYN

  val stateToString  : MetaSyn.State -> string
  val sgnToString    : MetaSyn.Sgn -> string
  val modeToString   : MetaSyn.Mode -> string
  val conDecToString  : IntSyn.ConDec -> string

end; (* module type METAPRINT *)
