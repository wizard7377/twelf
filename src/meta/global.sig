(* Global parameters *)
(* Author: Carsten Schuermann *)

signature MTPGLOBAL =
sig
  datatype prover_type = New | Old

  val prover : prover_type ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;  (* signature MTPGLOBAL *)
