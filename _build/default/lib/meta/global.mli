(* Global parameters *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPGLOBAL =
sig
  datatype prover_type = New | Old

  val prover : prover_type ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end (* GEN END SIGNATURE DECLARATION *);  (* signature MTPGLOBAL *)
