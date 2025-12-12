(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature CPRINT =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val goalToString: string -> IntSyn.dctx * CompSyn.goal -> string
  val clauseToString: string -> IntSyn.dctx * CompSyn.res_goal -> string
  val sProgToString: unit -> string
  val dProgToString: CompSyn.d_prog -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.conjunction -> string

end (* GEN END SIGNATURE DECLARATION *); (* signature CPRINT *)
