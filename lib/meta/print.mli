(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPRINT =
sig
  structure Formatter : FORMATTER
  structure StateSyn : STATESYN

  exception Error of string 

  val nameState : StateSyn.state -> StateSyn.state
  val formatState : StateSyn.state -> Formatter.format 
  val stateToString : StateSyn.state -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature MTPRINT *)
