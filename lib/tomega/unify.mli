(* Unification on Formulas *)

(* Author: Carsten Schuermann *)

module type TOMEGAUNIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Unify of string

  val unifyFor : Tomega.dec IntSyn.ctx * Tomega.for_sml * Tomega.for_sml -> unit
end

(* Signature TOMEGATYPECHECK *)
