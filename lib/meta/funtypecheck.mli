(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

module type FUNTYPECHECK = 
sig
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val isFor : IntSyn.dctx * FunSyn.for -> unit
  val check : FunSyn.pro * FunSyn.for -> unit    
  val checkSub : FunSyn.lfctx * IntSyn.Sub * FunSyn.lfctx -> unit

  val isState : StateSyn.state -> unit
end (* Signature FUNTYPECHECK *)       

