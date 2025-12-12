(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature FUNPRINT =
sig
  (*! structure FunSyn : FUNSYN !*)
  structure Formatter : FORMATTER

  val formatForBare : IntSyn.dctx * FunSyn.for -> Formatter.format
  val formatFor : FunSyn.lfctx * FunSyn.for -> string list -> Formatter.format
  val formatPro : FunSyn.lfctx * FunSyn.pro -> string list -> Formatter.format
  val formatLemmaDec: FunSyn.lemma_dec -> Formatter.format

  val forToString : FunSyn.lfctx * FunSyn.for -> string list -> string
  val proToString : FunSyn.lfctx * FunSyn.pro -> string list -> string
  val lemmaDecToString : FunSyn.lemma_dec -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature PRINT *)

