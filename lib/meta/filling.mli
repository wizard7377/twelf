(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPFILLING = 
sig
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string
  exception TimeOut

  type operator

  val expand : StateSyn.State -> operator 
  val apply : operator -> (int * FunSyn.Pro)
  val menu : operator -> string
end; (* module type MTPFILLING *)


