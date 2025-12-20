(* Meta printer for_sml proof states *)


(* Author: Carsten Schuermann *)


module type METAPRINT = sig
  module MetaSyn : METASYN
  val stateToString : MetaSyn.state -> string
  val sgnToString : MetaSyn.sgn -> string
  val modeToString : MetaSyn.mode -> string
  val conDecToString : IntSyn.conDec -> string

end


(* signature METAPRINT *)

