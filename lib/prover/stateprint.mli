(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

module type STATEPRINT =
sig
  module Formatter : FORMATTER

  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)
  module State : STATE

  exception Error of string 

  val nameState : State.State -> State.State
  val formatState : State.State -> Formatter.format 
  val stateToString : State.State -> string
end;  (* module type STATEPRINT *)
