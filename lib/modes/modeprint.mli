(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

module type MODEPRINT =
sig
  (*! module ModeSyn : MODESYN !*)

  val modeToString : IntSyn.cid * ModeSyn.ModeSpine -> string
  val modesToString : (IntSyn.cid * ModeSyn.ModeSpine) list -> string
end;  (* module type MODEPRINT *)
