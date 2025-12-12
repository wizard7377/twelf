(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature STATEPRINT =
sig
  structure Formatter : FORMATTER

  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  structure State : STATE

  exception Error of string 

  val nameState : State.state -> State.state
  val formatState : State.state -> Formatter.format 
  val stateToString : State.state -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature STATEPRINT *)
