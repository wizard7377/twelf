(* Inference: Version 1.3 *)
(* Author: Carsten Schuermann *)

module type INFERENCE = 
sig
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.state -> operator 
  val apply : operator -> StateSyn.state
  val menu : operator -> string
end;; (* module type Inference *)


