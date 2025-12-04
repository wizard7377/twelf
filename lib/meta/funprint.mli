(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

module type FUNPRINT =
sig
  (*! module FunSyn : FUNSYN !*)
  module Formatter : FORMATTER

  val formatForBare : IntSyn.dctx * FunSyn.for -> Formatter.format
  val formatFor : FunSyn.lfctx * FunSyn.for -> string list -> Formatter.format
  val formatPro : FunSyn.lfctx * FunSyn.pro -> string list -> Formatter.format
  val formatLemmaDec: FunSyn.lemmaDec -> Formatter.format

  val forToString : FunSyn.lfctx * FunSyn.for -> string list -> string
  val proToString : FunSyn.lfctx * FunSyn.pro -> string list -> string
  val lemmaDecToString : FunSyn.lemmaDec -> string
end;  (* module type PRINT *)

