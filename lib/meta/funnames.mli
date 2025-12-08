(* Names of Constants and Variables *)
(* Author: Carsten Schuermann *)

module type FUNNAMES =
sig

  (*! module FunSyn : FUNSYN !*)

  exception Error of string

  (* Constant names and fixities *)
  val reset : unit -> unit

  val installName : string * FunSyn.lemma -> unit
  val nameLookup : string -> FunSyn.lemma option
  val constName : FunSyn.lemma -> string	(* will mark if shadowed *)

end;; (* module type NAMES *)
