(* Filling: Version 1.4 *)
(* Author: Carsten Schuermann *)

module type FILL = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)
  module State  : STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end; (* module type FILL *)


