(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

module type ABSMACHINE =
sig

  (*! module IntSyn : INTSYN !*)
  (*! module CompSyn : COMPSYN !*)

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (IntSyn.exp -> unit) -> unit

end;; (* module type ABSMACHINE *)
