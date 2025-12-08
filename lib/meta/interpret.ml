(* Operational semantics *)
(* Author: Carsten Schuermann *)

module type Interpreter = 
sig
  (*! (FunSyn : FUNSYN) !*)

  let run : FunSyn.Pro -> FunSyn.Pro
end (* Signature Interpreter *)       
