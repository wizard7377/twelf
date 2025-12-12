(* Global parameters *)
(* Author: Carsten Schuermann *)

structure MetaGlobal : METAGLOBAL =
struct
  datatype strategy = RFS | FRS

  (* GEN BEGIN TAG INSIDE LET *) val strategy = ref FRS (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val maxFill = ref 6 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val maxSplit = ref 2 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val maxRecurse = ref 10 (* GEN END TAG INSIDE LET *)
end; (* structure MetaGlobal *)
