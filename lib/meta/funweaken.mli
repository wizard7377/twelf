(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

module type FUNWEAKEN = 
sig
  (*! module FunSyn : FUNSYN !*)

  val strengthenPsi : (FunSyn.lfctx * IntSyn.Sub) 
                  -> (FunSyn.lfctx * IntSyn.Sub)
  val strengthenPsi': (FunSyn.lfDec list * IntSyn.Sub) 
                  -> (FunSyn.lfDec list * IntSyn.Sub) 
end (* module type FUNWEAKEN *)