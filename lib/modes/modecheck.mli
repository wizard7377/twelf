(* Mode Checking *)


(* Author: Carsten Schuermann *)


(* Modified: Frank Pfenning *)


module type MODECHECK = sig
  exception Error of string
(* for_sml new declarations *)
  val checkD : IntSyn.conDec * string * Paths.occConDec option -> unit
(* raises Error (msg) *)
(* for_sml prior declarations *)
  val checkMode : IntSyn.cid * ModeSyn.modeSpine -> unit
(* raises Error(msg) *)
(* for_sml output coverage of prior declarations *)
  val checkFreeOut : IntSyn.cid * ModeSyn.modeSpine -> unit
(* raises Error(msg) *)

end


(* signature MODECHECK *)

