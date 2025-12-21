(* Weakening substitutions for_sml meta substitutions *)

(* Author: Carsten Schuermann *)

module type FUNWEAKEN = sig
  (*! structure FunSyn : FUNSYN !*)
  val strengthenPsi : FunSyn.lfctx * IntSyn.sub -> FunSyn.lfctx * IntSyn.sub

  val strengthenPsi' :
    FunSyn.lFDec list * IntSyn.sub -> FunSyn.lFDec list * IntSyn.sub
end

(* signature FUNWEAKEN *)
