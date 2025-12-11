(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)

signature TOMEGAABSTRACT = 
sig
  exception Error of string
  val raiseFor : IntSyn.dec IntSyn.ctx * (Tomega.for * IntSyn.sub) -> Tomega.for
  val raisePrg : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for -> Tomega.prg
  val raiseP   : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for -> Tomega.prg
  val raiseF   : IntSyn.dec IntSyn.ctx * (Tomega.for * IntSyn.sub) -> Tomega.for
end (* Signature TOMEGAABSTRACT *)       

