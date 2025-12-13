(* Global parameters *)
(* Author: Carsten Schuermann *)

structure MetaGlobal : METAGLOBAL =
struct
  datatype strategy = RFS | FRS

  (* GEN BEGIN TAG OUTSIDE LET *) val strategy = ref FRS (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxFill = ref 6 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxSplit = ref 2 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxRecurse = ref 10 (* GEN END TAG OUTSIDE LET *)
end; (* structure MetaGlobal *)
