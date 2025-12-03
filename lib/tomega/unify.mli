(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

module type TOMEGAUNIFY = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)

  exception Unify of string

  val unifyFor : Tomega.Dec IntSyn.Ctx * Tomega.For * Tomega.For -> unit
end (* Signature TOMEGATYPECHECK *)       

