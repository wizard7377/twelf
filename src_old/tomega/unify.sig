(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

signature TOMEGAUNIFY = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Unify of string

  val unifyFor : Tomega.dec IntSyn.ctx * Tomega.for * Tomega.for -> unit
end (* Signature TOMEGATYPECHECK *)       

