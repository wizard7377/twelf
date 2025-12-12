(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature OPSEM = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception NoMatch

  val evalPrg : Tomega.prg -> Tomega.prg
  val topLevel : Tomega.prg -> unit
  val createVarSub : Tomega.dec IntSyn.ctx * Tomega.dec IntSyn.ctx -> Tomega.sub
  val matchSub : Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.sub -> unit
end (* GEN END SIGNATURE DECLARATION *)
