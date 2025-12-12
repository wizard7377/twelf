(* Worldify *) 
(* Author: Carsten Schuermann *)


(* GEN BEGIN SIGNATURE DECLARATION *) signature WORLDIFY = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string 

  val worldify :  IntSyn.cid -> IntSyn.con_dec list
  val worldifyGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> IntSyn.exp
(*  val check : Tomega.Worlds -> IntSyn.cid list -> unit
  val closure : Tomega.Worlds -> Tomega.Worlds *)
end (* GEN END SIGNATURE DECLARATION *); (* signature WORLDIFY *)
