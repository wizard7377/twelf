(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

module type ABSMACHINESBT =
sig

  (*! module IntSyn  : INTSYN !*)
  (*! module CompSyn : COMPSYN !*)

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.Flatterm list -> unit) -> unit 


end;  (* module type ABSMACHINESBT *)
