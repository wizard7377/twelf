(* Weakening substitutions *)
(* Author: Carsten Schuermann *)

module type WEAKEN = 
sig
  (*! module IntSyn : INTSYN !*)

  val strengthenExp : (IntSyn.exp * IntSyn.Sub) -> IntSyn.exp
  val strengthenSpine: (IntSyn.Spine * IntSyn.Sub) -> IntSyn.Spine
  val strengthenCtx : (IntSyn.dctx * IntSyn.Sub) -> (IntSyn.dctx * IntSyn.Sub)
  val strengthenDec : (IntSyn.Dec * IntSyn.Sub) -> IntSyn.Dec
  val strengthenSub : (IntSyn.Sub * IntSyn.Sub) -> IntSyn.Sub
end (* module type PRUNE *)