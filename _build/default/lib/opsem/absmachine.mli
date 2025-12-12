(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature ABSMACHINE =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val solve     : (CompSyn.goal * IntSyn.sub) * CompSyn.d_prog
                  * (IntSyn.exp -> unit) -> unit

end (* GEN END SIGNATURE DECLARATION *);  (* signature ABSMACHINE *)
