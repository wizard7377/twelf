(* Operational semantics *)

(* Author: Carsten Schuermann *)

module type Interpreter = sig
  (*! structure FunSyn : FUNSYN !*)
  val run : FunSyn.pro -> FunSyn.pro
end

(* Signature Interpreter *)
