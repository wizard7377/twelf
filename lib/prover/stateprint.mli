(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

module type STATEPRINT =
sig
  module Formatter : FORMATTER

  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)
  module State : STATE

  exception Error of string 

  val nameState : State.state -> State.state
  val formatState : State.state -> Formatter.format 
  val stateToString : State.state -> string
end;  (* module type STATEPRINT *)
