open Basis
(* Global parameters *)

(* Author: Carsten Schuermann *)

module type MTPGLOBAL = sig
  type proverType = New | Old

  val prover : proverType ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end

(* signature MTPGLOBAL *)
(* Meta Global parameters *)

(* Author: Carsten Schuermann *)

module MTPGlobal (MetaGlobal : Meta_global.METAGLOBAL) : MTPGLOBAL = struct
  type proverType = New | Old

  let prover = ref New
  let maxFill = MetaGlobal.maxFill
  let maxSplit = MetaGlobal.maxSplit
  let maxRecurse = MetaGlobal.maxRecurse
end

(* structure MTPGlobal *)
