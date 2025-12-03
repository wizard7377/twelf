(* Initialization *)
(* Author: Carsten Schuermann *)

module type MTPINIT = 
sig
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  (* Current restriction to non-mutual inductive theorems ! *)
     
  val init : (FunSyn.For * StateSyn.Order) -> StateSyn.State list
 
end;  (* module type MTPINIT *)
