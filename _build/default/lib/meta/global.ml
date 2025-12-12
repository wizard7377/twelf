(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPGlobal
  (structure MetaGlobal : METAGLOBAL): MTPGLOBAL =
struct
  datatype prover_type = New | Old

  val prover = ref New
  val maxFill = MetaGlobal.maxFill
  val maxSplit = MetaGlobal.maxSplit
  val maxRecurse = MetaGlobal.maxRecurse
end (* GEN END FUNCTOR DECL *); (* structure MTPGlobal *)
