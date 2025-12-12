(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

signature TOMEGACOVERAGE = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string

  val coverageCheckPrg : Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg -> unit
end (* Signature TOMEGACOVERAGE *)       

