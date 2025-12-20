(* Abstraction mechanisms form programs and formulas *)


(* Author: Carsten Schuermann *)


module type TOMEGAABSTRACT = sig
  exception Error of string
  val raiseFor : IntSyn.dec IntSyn.ctx * (Tomega.for_sml * IntSyn.sub) -> Tomega.for_sml
  val raisePrg : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml -> Tomega.prg
  val raiseP : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml -> Tomega.prg
  val raiseF : IntSyn.dec IntSyn.ctx * (Tomega.for_sml * IntSyn.sub) -> Tomega.for_sml

end

(* Signature TOMEGAABSTRACT *)

