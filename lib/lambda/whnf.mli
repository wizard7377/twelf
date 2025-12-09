(* Weak Head-Normal Forms *)
(* Authors: Frank Pfenning, Carsten Schuermann *)

module type WHNF =
sig
  (*! module IntSyn : INTSYN !*)

  (* Patterns *)
  val isPatSub : IntSyn.Sub -> bool
  val makePatSub : IntSyn.Sub -> IntSyn.Sub option
  val dotEta   : IntSyn.Front * IntSyn.Sub -> IntSyn.Sub

  exception Eta
  val etaContract : IntSyn.exp -> int	(* can raise Eta *)

  (* Weak head normalization *)
  val whnf : IntSyn.eclo -> IntSyn.eclo
  val expandDef : IntSyn.eclo -> IntSyn.eclo
  val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
  val etaExpandRoot : IntSyn.exp -> IntSyn.exp
  val whnfEta : (IntSyn.eclo * IntSyn.eclo) -> (IntSyn.eclo * IntSyn.eclo)
  val lowerEVar : IntSyn.exp -> IntSyn.exp

  val newLoweredEVar : IntSyn.dctx * IntSyn.eclo -> IntSyn.exp
  val newSpineVar : IntSyn.dctx * IntSyn.eclo -> IntSyn.Spine
  val spineToSub : IntSyn.Spine * IntSyn.Sub -> IntSyn.Sub

  (* Full normalization *)
  val normalize: IntSyn.eclo -> IntSyn.exp
  val normalizeDec: IntSyn.dec * IntSyn.Sub -> IntSyn.Dec
  val normalizeCtx: IntSyn.dctx -> IntSyn.dctx

  (* Inverting substitutions *)
  val invert : IntSyn.Sub -> IntSyn.Sub
  val strengthen: IntSyn.Sub * IntSyn.dctx -> IntSyn.dctx 
  val isId : IntSyn.Sub -> bool

  val cloInv : IntSyn.exp * IntSyn.Sub -> IntSyn.exp
  val compInv : IntSyn.Sub * IntSyn.Sub -> IntSyn.Sub
end;; (* module type WHNF *)
