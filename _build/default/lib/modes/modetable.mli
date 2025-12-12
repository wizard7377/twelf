(* Mode Table *)
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MODETABLE =
sig

  exception Error of string

  val reset : unit -> unit

  (* single mode installation and lookup *)
  val installMode : (IntSyn.cid * ModeSyn.mode_spine) -> unit 
  val modeLookup : IntSyn.cid -> ModeSyn.mode_spine option
  val uninstallMode : IntSyn.cid -> bool (* true: was declared, false: not *)

  (* multiple mode installation and lookup *)
  val installMmode : (IntSyn.cid * ModeSyn.mode_spine) -> unit 
  val mmodeLookup : IntSyn.cid -> ModeSyn.mode_spine list

end (* GEN END SIGNATURE DECLARATION *);  (* signature MODETABLE *)
