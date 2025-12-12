(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature ABSMACHINESBT =
sig

  (*! structure IntSyn  : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val solve     : (CompSyn.goal * IntSyn.sub) * CompSyn.d_prog
                  * (CompSyn.flatterm list -> unit) -> unit 


end (* GEN END SIGNATURE DECLARATION *);  (* signature ABSMACHINESBT *)
