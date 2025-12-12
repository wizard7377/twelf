(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature RELFUN = 
sig
  (*! structure FunSyn : FUNSYN !*)

  exception Error of string

  val convertFor : IntSyn.cid list -> FunSyn.for
  val convertPro : IntSyn.cid list -> FunSyn.pro
end (* GEN END SIGNATURE DECLARATION *) (* Signature RELFUN *)       


