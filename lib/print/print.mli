(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

module type PRINT =
sig
  (*! module IntSyn : INTSYN !*)
  module Formatter : FORMATTER

  val implicit : bool ref
  val printInfix : bool ref
  val printDepth : int option ref
  val printLength : int option ref
  val noShadow : bool ref

  val formatDec : IntSyn.dctx * IntSyn.dec -> Formatter.format
  val formatDecList : IntSyn.dctx * IntSyn.dec list -> Formatter.format
  val formatDecList' : IntSyn.dctx * (IntSyn.dec list * IntSyn.Sub) -> Formatter.format
  val formatExp : IntSyn.dctx * IntSyn.exp -> Formatter.format
  val formatSpine : IntSyn.dctx * IntSyn.Spine -> Formatter.format list
  val formatConDec : IntSyn.conDec -> Formatter.format
  val formatConDecI : IntSyn.conDec -> Formatter.format
  val formatCnstr : IntSyn.Cnstr -> Formatter.format
  val formatCtx : IntSyn.dctx * IntSyn.dctx -> Formatter.format

  val decToString : IntSyn.dctx * IntSyn.dec -> string
  val expToString : IntSyn.dctx * IntSyn.exp -> string
  val conDecToString : IntSyn.conDec -> string
  val cnstrToString : IntSyn.Cnstr -> string
  val cnstrsToString : IntSyn.cnstr list -> string (* assigns names in contexts *)
  val ctxToString : IntSyn.dctx * IntSyn.dctx -> string

  val evarInstToString : (IntSyn.exp * string) list -> string
  val evarCnstrsToStringOpt : (IntSyn.exp * string) list -> string option

  val formatWorlds : Tomega.Worlds -> Formatter.format 
  val worldsToString : Tomega.Worlds -> string

  val printSgn : unit -> unit

end;; (* module type PRINT *)
