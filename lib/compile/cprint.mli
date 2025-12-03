(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

module type CPRINT =
sig

  (*! module IntSyn : INTSYN !*)
  (*! module CompSyn : COMPSYN !*)

  val goalToString: string -> IntSyn.dctx * CompSyn.Goal -> string
  val clauseToString: string -> IntSyn.dctx * CompSyn.ResGoal -> string
  val sProgToString: unit -> string
  val dProgToString: CompSyn.DProg -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.Conjunction -> string

end; (* module type CPRINT *)
