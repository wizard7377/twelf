(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MODEPRINT =
sig
  (*! structure ModeSyn : MODESYN !*)

  val modeToString : IntSyn.cid * ModeSyn.mode_spine -> string
  val modesToString : (IntSyn.cid * ModeSyn.mode_spine) list -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature MODEPRINT *)
