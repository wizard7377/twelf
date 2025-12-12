(* ELIM: Version 1.4 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature ELIM = 
sig
  structure State : STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list 
  val apply : operator -> unit
  val menu : operator -> string
end (* GEN END SIGNATURE DECLARATION *); (* signature ELIM *)


