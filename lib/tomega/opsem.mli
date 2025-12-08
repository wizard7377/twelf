(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)

module type OPSEM = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)

  exception NoMatch

  val evalPrg : Tomega.Prg -> Tomega.Prg
  val topLevel : Tomega.Prg -> unit
  val createVarSub : Tomega.Dec IntSyn.ctx * Tomega.Dec IntSyn.ctx -> Tomega.Sub
  val matchSub : Tomega.Dec IntSyn.ctx * Tomega.Sub * Tomega.Sub -> unit
end
