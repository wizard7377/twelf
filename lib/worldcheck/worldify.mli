(* Worldify *) 
(* Author: Carsten Schuermann *)


module type WORLDIFY = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)

  exception Error of string 

  val worldify :  IntSyn.cid -> IntSyn.conDec list
  val worldifyGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> IntSyn.exp
(*  val check : Tomega.Worlds -> IntSyn.cid list -> unit
  val closure : Tomega.Worlds -> Tomega.Worlds *)
end;; (* module type WORLDIFY *)
