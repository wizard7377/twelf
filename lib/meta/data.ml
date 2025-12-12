(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPData (structure MTPGlobal : MTPGLOBAL) : MTPDATA =
struct
  val maxFill = ref 0
end (* GEN END FUNCTOR DECL *); (* structure MTPData*)
