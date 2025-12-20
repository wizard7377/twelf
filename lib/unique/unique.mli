(* Uniqueness Checking *)


(* Author: Frank Pfenning *)


module type UNIQUE = sig
  exception Error of string
  val checkUnique : (IntSyn.cid * ModeSyn.modeSpine) -> unit
(* raises Error(msg) *)

end


(* signature UNIQUE *)

