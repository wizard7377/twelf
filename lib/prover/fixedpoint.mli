(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)

module type FIXEDPOINT = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA !*)
  module State : STATE

  exception Error of string

  type operator

  val expand : (State.Focus * Tomega.TC) -> operator
  val apply : operator -> unit
  val menu : operator -> string
end; (* module type Fixed Point *)


