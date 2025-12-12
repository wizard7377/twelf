(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature CLAUSEPRINT =
sig

  (*! structure IntSyn : INTSYN !*)
  structure Formatter : FORMATTER

  val formatClause : IntSyn.dctx * IntSyn.exp -> Formatter.format
  val formatConDec : IntSyn.con_dec -> Formatter.format

  val clauseToString : IntSyn.dctx * IntSyn.exp -> string
  val conDecToString : IntSyn.con_dec -> string

  val printSgn : unit -> unit

end;  (* signature CLAUSEPRINT *)
