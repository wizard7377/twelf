(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)

module type TOMEGATYPECHECK = 
sig
  exception Error of string

  val checkCtx : Tomega.Dec IntSyn.ctx -> unit
  val checkFor : Tomega.Dec IntSyn.ctx * Tomega.For -> unit
  val checkPrg : Tomega.Dec IntSyn.ctx * (Tomega.Prg * Tomega.For) -> unit    
  val checkSub : Tomega.Dec IntSyn.ctx * Tomega.Sub * Tomega.Dec IntSyn.ctx -> unit
end (* Signature TOMEGATYPECHECK *)       

