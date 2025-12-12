(* Operational semantics *)
(* Author: Carsten Schuermann *)

signature Interpreter = 
sig
  (*! structure FunSyn : FUNSYN !*)

  val run : FunSyn.pro -> FunSyn.pro
end (* Signature Interpreter *)       
