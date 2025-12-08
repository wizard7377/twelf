(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

module type TOMEGACOVERAGE = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)

  exception Error of string

  val coverageCheckPrg : Tomega.Worlds * Tomega.Dec IntSyn.ctx * Tomega.Prg -> unit
end (* Signature TOMEGACOVERAGE *)       

