open Basis
(* Recurse: Version 1.4 *)

(* Author: Carsten Schuermann *)

module type RECURSE = sig
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end

(* signature RECURSE *)
