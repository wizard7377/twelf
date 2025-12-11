(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

signature RELFUN = 
sig
  (*! structure FunSyn : FUNSYN !*)

  exception Error of string

  val convertFor : IntSyn.cid list -> FunSyn.for
  val convertPro : IntSyn.cid list -> FunSyn.pro
end (* Signature RELFUN *)       


