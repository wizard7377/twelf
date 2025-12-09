(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type CLAUSEPRINT =
sig

  (*! module IntSyn : INTSYN !*)
  module Formatter : FORMATTER

  val formatClause : IntSyn.dctx * IntSyn.exp -> Formatter.format
  val formatConDec : IntSyn.conDec -> Formatter.format

  val clauseToString : IntSyn.dctx * IntSyn.exp -> string
  val conDecToString : IntSyn.conDec -> string

  val printSgn : unit -> unit

end;; (* module type CLAUSEPRINT *)
