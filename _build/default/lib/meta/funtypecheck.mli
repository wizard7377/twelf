(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature FUNTYPECHECK = 
sig
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string

  val isFor : IntSyn.dctx * FunSyn.for -> unit
  val check : FunSyn.pro * FunSyn.for -> unit    
  val checkSub : FunSyn.lfctx * IntSyn.sub * FunSyn.lfctx -> unit

  val isState : StateSyn.state -> unit
end (* GEN END SIGNATURE DECLARATION *) (* Signature FUNTYPECHECK *)       

