(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)

module type TOMEGAABSTRACT = 
sig
  exception Error of string
  val raiseFor : IntSyn.dec IntSyn.ctx * (Tomega.For * IntSyn.Sub) -> Tomega.For
  val raisePrg : IntSyn.dec IntSyn.ctx * Tomega.Prg * Tomega.For -> Tomega.Prg
  val raiseP   : IntSyn.dec IntSyn.ctx * Tomega.Prg * Tomega.For -> Tomega.Prg
  val raiseF   : IntSyn.dec IntSyn.ctx * (Tomega.For * IntSyn.Sub) -> Tomega.For
end (* Signature TOMEGAABSTRACT *)       

