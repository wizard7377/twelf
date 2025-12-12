(* Names of Constants and Variables *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature FUNNAMES =
sig

  (*! structure FunSyn : FUNSYN !*)

  exception Error of string

  (* Constant names and fixities *)
  val reset : unit -> unit

  val installName : string * FunSyn.lemma -> unit
  val nameLookup : string -> FunSyn.lemma option
  val constName : FunSyn.lemma -> string	(* will mark if shadowed *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature NAMES *)
