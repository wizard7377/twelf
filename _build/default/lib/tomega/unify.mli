(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature TOMEGAUNIFY = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Unify of string

  val unifyFor : Tomega.dec IntSyn.ctx * Tomega.for * Tomega.for -> unit
end (* GEN END SIGNATURE DECLARATION *) (* Signature TOMEGATYPECHECK *)       

