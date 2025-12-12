(* Weakening substitutions *)
(* Author: Carsten Schuermann *)

signature WEAKEN = 
sig
  (*! structure IntSyn : INTSYN !*)

  val strengthenExp : (IntSyn.exp * IntSyn.sub) -> IntSyn.exp
  val strengthenSpine: (IntSyn.spine * IntSyn.sub) -> IntSyn.spine
  val strengthenCtx : (IntSyn.dctx * IntSyn.sub) -> (IntSyn.dctx * IntSyn.sub)
  val strengthenDec : (IntSyn.dec * IntSyn.sub) -> IntSyn.dec
  val strengthenSub : (IntSyn.sub * IntSyn.sub) -> IntSyn.sub
end (* signature PRUNE *)