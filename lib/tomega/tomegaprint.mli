(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

module type TOMEGAPRINT =
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Tomega : TOMEGA  !*)
  module Formatter : FORMATTER

  exception Error of string

  val formatFor   : Tomega.Dec IntSyn.ctx * Tomega.For -> Formatter.format
  val forToString : Tomega.Dec IntSyn.ctx * Tomega.For -> string
  val formatFun : (string list * Tomega.lemma list) * Tomega.Prg -> Formatter.format
    
  val formatPrg : Tomega.Dec IntSyn.ctx * Tomega.Prg -> Formatter.format
(*  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format *)

  val funToString : (string list * Tomega.lemma list) * Tomega.Prg -> string
  (* funToString ((names, projs), P)  = s
     cids is the list of mututal recursive type families.  (could also be names)
     projs are the projection functions used internally,  They must be in the
     same order as names.  The nth name corresponds to the nth projection function
  *)
     
  val evarReset : unit -> unit
  val evarName : string -> Tomega.Prg
  val nameEVar : Tomega.Prg -> string

  val prgToString : Tomega.Dec IntSyn.ctx * Tomega.Prg -> string
    
  val nameCtx   : Tomega.Dec IntSyn.ctx -> Tomega.Dec IntSyn.ctx
  val formatCtx : Tomega.Dec IntSyn.ctx -> Formatter.format
  val ctxToString : Tomega.Dec IntSyn.ctx -> string

(*  val lemmaDecToString : FunSyn.LemmaDec -> string *)
end;; (* module type TOMEGAPRINT *)

