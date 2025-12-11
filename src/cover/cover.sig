(* Coverage Checking *)
(* Author: Frank Pfenning *)

signature COVER =
sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit	(* raises Error(msg) *)

  val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit

  val checkCovers : (IntSyn.cid * ModeSyn.mode_spine) -> unit

  val coverageCheckCases : Tomega.worlds * (IntSyn.dctx * IntSyn.sub) list  * IntSyn.dctx -> unit

end;  (* signature COVER *)
