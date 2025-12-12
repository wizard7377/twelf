(* Global parameters *)
(* Author: Carsten Schuermann *)

structure MetaGlobal : METAGLOBAL =
struct
  datatype strategy = RFS | FRS

  val strategy = ref FRS
  val maxFill = ref 6
  val maxSplit = ref 2
  val maxRecurse = ref 10
end; (* structure MetaGlobal *)
