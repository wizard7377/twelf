(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature TOMEGACOVERAGE = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string

  val coverageCheckPrg : Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg -> unit
end (* GEN END SIGNATURE DECLARATION *) (* Signature TOMEGACOVERAGE *)       

