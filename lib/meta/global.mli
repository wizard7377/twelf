(* Global parameters *)
(* Author: Carsten Schuermann *)

module type MTPGLOBAL =
sig
  type proverType = New | Old

  val prover : ProverType ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;; (* module type MTPGLOBAL *)
