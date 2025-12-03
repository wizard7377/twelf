(* Coverage Checking *)
(* Author: Frank Pfenning *)

module type COVER =
sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit	(* raises Error(msg) *)

  val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit

  val checkCovers : (IntSyn.cid * ModeSyn.ModeSpine) -> unit

  val coverageCheckCases : Tomega.Worlds * (IntSyn.dctx * IntSyn.Sub) list  * IntSyn.dctx -> unit

end;  (* module type COVER *)
