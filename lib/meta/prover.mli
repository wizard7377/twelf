(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)


module type MTPROVER =
sig
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string 

  val init : FunSyn.for * StateSyn.order -> unit
end;  (* module type MTPROVER *)
