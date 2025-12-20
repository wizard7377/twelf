(* Global parameters *)


(* Author: Carsten Schuermann *)


module type MTPGLOBAL = sig
  type proverType = New | Old
  val prover : proverType ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref

end


(* signature MTPGLOBAL *)

