(* Printing Mode Declarations *)


(* Author: Carsten Schuermann *)


module type MODEPRINT = sig
(*! structure ModeSyn : MODESYN !*)
  val modeToString : IntSyn.cid * ModeSyn.modeSpine -> string
  val modesToString : IntSyn.cid * ModeSyn.modeSpine list -> string

end


(* signature MODEPRINT *)

