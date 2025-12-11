(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

signature MODEPRINT =
sig
  (*! structure ModeSyn : MODESYN !*)

  val modeToString : IntSyn.cid * ModeSyn.mode_spine -> string
  val modesToString : (IntSyn.cid * ModeSyn.mode_spine) list -> string
end;  (* signature MODEPRINT *)
