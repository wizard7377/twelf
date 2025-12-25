open Basis ;; 
(* Operational semantics *)

(* Author: Carsten Schuermann *)

module type Interpreter = sig
  (*! structure FunSyn : Funsyn.FUNSYN !*)
  val run : FunSyn.pro -> FunSyn.pro
end

(* Signature Interpreter *)
