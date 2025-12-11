(* Recurse: Version 1.4 *)
(* Author: Carsten Schuermann *)

signature RECURSE = 
sig
  structure State : STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list 
  val apply : operator -> unit
  val menu : operator -> string
end; (* signature RECURSE *)


