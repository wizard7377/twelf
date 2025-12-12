(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPFILLING = 
sig
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string
  exception TimeOut

  type operator

  val expand : StateSyn.state -> operator 
  val apply : operator -> (int * FunSyn.pro)
  val menu : operator -> string
end (* GEN END SIGNATURE DECLARATION *); (* signature MTPFILLING *)


