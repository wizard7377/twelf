(* Printer for_sml Compiled Syntax *)


(* Author: Iliano Cervesato *)


module type CPRINT = sig
(*! structure IntSyn : INTSYN !*)
(*! structure CompSyn : COMPSYN !*)
  val goalToString : string -> IntSyn.dctx * CompSyn.goal -> string
  val clauseToString : string -> IntSyn.dctx * CompSyn.resGoal -> string
  val sProgToString : unit -> string
  val dProgToString : CompSyn.dProg -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.conjunction -> string

end


(* signature CPRINT *)

