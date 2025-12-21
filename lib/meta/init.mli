(* Initialization *)

(* Author: Carsten Schuermann *)

module type MTPINIT = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  (* Current restriction to non-mutual inductive theorems ! *)
  val init : FunSyn.for_sml * StateSyn.order -> StateSyn.state list
end

(* signature MTPINIT *)
