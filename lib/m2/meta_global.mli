(* Global parameters *)
(* Author: Carsten Schuermann *)

module type METAGLOBAL =
sig
  type strategy = RFS | FRS

  val strategy : Strategy ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;; (* module type METAGLOBAL *)
