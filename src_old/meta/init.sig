(* Initialization *)
(* Author: Carsten Schuermann *)

signature MTPINIT = 
sig
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string

  (* Current restriction to non-mutual inductive theorems ! *)
     
  val init : (FunSyn.for * StateSyn.order) -> StateSyn.state list
 
end;  (* signature MTPINIT *)
