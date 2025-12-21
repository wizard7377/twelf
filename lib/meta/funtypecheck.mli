(* Type checking for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

module type FUNTYPECHECK = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val isFor : IntSyn.dctx * FunSyn.for_sml -> unit
  val check : FunSyn.pro * FunSyn.for_sml -> unit
  val checkSub : FunSyn.lfctx * IntSyn.sub * FunSyn.lfctx -> unit
  val isState : StateSyn.state -> unit
end

(* Signature FUNTYPECHECK *)
