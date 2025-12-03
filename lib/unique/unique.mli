(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

module type UNIQUE =
sig

  exception Error of string

  val checkUnique : (IntSyn.cid * ModeSyn.ModeSpine) -> unit  (* raises Error(msg) *)

end;  (* module type UNIQUE *)
