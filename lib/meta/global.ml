(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPGlobal
  (structure MetaGlobal : METAGLOBAL): MTPGLOBAL =
struct
  datatype prover_type = New | Old

  (* GEN BEGIN TAG OUTSIDE LET *) val prover = ref New (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxFill = MetaGlobal.maxFill (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxSplit = MetaGlobal.maxSplit (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxRecurse = MetaGlobal.maxRecurse (* GEN END TAG OUTSIDE LET *)
end (* GEN END FUNCTOR DECL *); (* structure MTPGlobal *)
