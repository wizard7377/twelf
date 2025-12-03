(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPRINT =
sig
  module Formatter : FORMATTER
  module StateSyn : STATESYN

  exception Error of string 

  val nameState : StateSyn.State -> StateSyn.State
  val formatState : StateSyn.State -> Formatter.format 
  val stateToString : StateSyn.State -> string
end;  (* module type MTPRINT *)
