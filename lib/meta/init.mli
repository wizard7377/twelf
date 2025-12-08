(* Initialization *)
(* Author: Carsten Schuermann *)

module type MTPINIT = 
sig
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  (* Current restriction to non-mutual inductive theorems ! *)
     
  val init : (FunSyn.for * StateSyn.order) -> StateSyn.state list
 
end;; (* module type MTPINIT *)
