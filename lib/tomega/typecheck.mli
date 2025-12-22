(* Type checking for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

(* Modified: Yu Liao *)

module type TOMEGATYPECHECK = sig
  exception Error of string

  val checkCtx : Tomega.dec IntSyn.ctx -> unit
  val checkFor : Tomega.dec IntSyn.ctx * Tomega.for_sml -> unit
  val checkPrg : Tomega.dec IntSyn.ctx * (Tomega.prg * Tomega.for_sml) -> unit

  val checkSub :
    Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.dec IntSyn.ctx -> unit
end

(* Signature TOMEGATYPECHECK *)
