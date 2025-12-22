(* External Syntax for_sml signature entries *)

(* Author: Frank Pfenning *)

module type EXTCONDEC = sig
  module ExtSyn : EXTSYN

  (*! structure Paths : PATHS !*)
  type condec

  (* constant declaration *)
  val condec : string * ExtSyn.term -> condec

  (* id : tm *)
  val blockdec : string * ExtSyn.dec list * ExtSyn.dec list -> condec
  val blockdef : string * string list * string list -> condec
  val condef : string option * ExtSyn.term * ExtSyn.term option -> condec
  (* id : tm = tm | _ : tm = tm *)
end

(* signature EXTCONDEC *)

module type RECON_CONDEC = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTCONDEC

  exception Error of string

  val condecToConDec :
    condec * Paths.location * bool ->
    IntSyn.conDec option * Paths.occConDec option

  (* optional ConDec is absent for_sml anonymous definitions *)
  (* bool = true means that condec is an abbreviation *)
  val internalInst :
    IntSyn.conDec * IntSyn.conDec * Paths.region -> IntSyn.conDec

  val externalInst : IntSyn.conDec * ExtSyn.term * Paths.region -> IntSyn.conDec
end

(* signature RECON_CONDEC *)
