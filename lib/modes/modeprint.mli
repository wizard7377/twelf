(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

module type MODEPRINT =
sig
  (*! module ModeSyn : MODESYN !*)

  val modeToString : IntSyn.cid * ModeSyn.modeSpine -> string
  val modesToString : (IntSyn.cid * ModeSyn.modeSpine) list -> string
end;  (* module type MODEPRINT *)
