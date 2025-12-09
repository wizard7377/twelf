(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type ABSTRACT =
sig
  exception Error of string

  val piDepend  : (IntSyn.dec * IntSyn.Depend) * IntSyn.exp -> IntSyn.exp
  val closedDec : IntSyn.dec IntSyn.ctx * (IntSyn.dec * IntSyn.Sub) -> bool
  val closedSub : IntSyn.dec IntSyn.ctx * IntSyn.Sub -> bool
  val closedExp : IntSyn.dec IntSyn.ctx * (IntSyn.exp * IntSyn.Sub) -> bool
  val closedCtx : IntSyn.dec IntSyn.ctx -> bool
  val closedCTX : Tomega.Dec IntSyn.ctx -> bool

  val abstractDecImp : IntSyn.exp  -> (int * IntSyn.exp)
  val abstractDef : (IntSyn.exp * IntSyn.exp)
                     -> (int * (IntSyn.exp * IntSyn.exp))
  val abstractCtxs : (IntSyn.dec IntSyn.ctx) list
                     -> (IntSyn.dec IntSyn.ctx) * (IntSyn.dec IntSyn.ctx) list
  val abstractTomegaSub : Tomega.Sub -> (Tomega.Dec IntSyn.ctx * Tomega.Sub)
  val abstractTomegaPrg : Tomega.Prg -> (Tomega.Dec IntSyn.ctx * Tomega.Prg)
  val abstractSpine : IntSyn.Spine * IntSyn.Sub -> (IntSyn.dctx * IntSyn.Spine)

  val collectEVars : IntSyn.dctx * IntSyn.eclo * IntSyn.exp list -> IntSyn.exp list
  val collectEVarsSpine : IntSyn.dctx * (IntSyn.Spine * IntSyn.Sub) * IntSyn.exp list -> IntSyn.exp list
                         

  val raiseTerm    : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
  val raiseType    : IntSyn.dctx * IntSyn.exp -> IntSyn.exp

end;; (* module type ABSTRACT *)
