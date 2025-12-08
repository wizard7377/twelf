(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)

module type TOMEGAABSTRACT = 
sig
  exception Error of string
  val raiseFor : IntSyn.Dec IntSyn.ctx * (Tomega.For * IntSyn.Sub) -> Tomega.For
  val raisePrg : IntSyn.Dec IntSyn.ctx * Tomega.Prg * Tomega.For -> Tomega.Prg
  val raiseP   : IntSyn.Dec IntSyn.ctx * Tomega.Prg * Tomega.For -> Tomega.Prg
  val raiseF   : IntSyn.Dec IntSyn.ctx * (Tomega.For * IntSyn.Sub) -> Tomega.For
end (* Signature TOMEGAABSTRACT *)       

