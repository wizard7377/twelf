(* Modes: short and long forms *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MODEDEC =
sig
  exception  Error of string

  val shortToFull : IntSyn.cid * ModeSyn.mode_spine * Paths.region -> ModeSyn.mode_spine
  val checkFull : IntSyn.cid * ModeSyn.mode_spine * Paths.region -> unit
  val checkPure : (IntSyn.cid * ModeSyn.mode_spine) * Paths.region -> unit
 
end (* GEN END SIGNATURE DECLARATION *);  (* signature MODEDEC *)
