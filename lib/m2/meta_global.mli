(* Global parameters *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature METAGLOBAL =
sig
  datatype strategy = RFS | FRS

  val strategy : strategy ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end (* GEN END SIGNATURE DECLARATION *);  (* signature METAGLOBAL *)
