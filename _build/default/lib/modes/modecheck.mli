(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MODECHECK =
sig
  exception Error of string

  (* for new declarations *)
  val checkD : IntSyn.con_dec * string * Paths.occ_con_dec option -> unit  (* raises Error (msg) *)

  (* for prior declarations *)
  val checkMode : IntSyn.cid * ModeSyn.mode_spine -> unit (* raises Error(msg) *)

  (* for output coverage of prior declarations *)
  val checkFreeOut : IntSyn.cid * ModeSyn.mode_spine -> unit (* raises Error(msg) *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature MODECHECK *)
