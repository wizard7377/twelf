(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

signature UNIQUE =
sig

  exception Error of string

  val checkUnique : (IntSyn.cid * ModeSyn.mode_spine) -> unit  (* raises Error(msg) *)

end;  (* signature UNIQUE *)
