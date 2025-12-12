(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

signature FUNWEAKEN = 
sig
  (*! structure FunSyn : FUNSYN !*)

  val strengthenPsi : (FunSyn.lfctx * IntSyn.sub) 
                  -> (FunSyn.lfctx * IntSyn.sub)
  val strengthenPsi': (FunSyn.lf_dec list * IntSyn.sub) 
                  -> (FunSyn.lf_dec list * IntSyn.sub) 
end (* signature FUNWEAKEN *)