(* External Syntax for module type entries *)
(* Author: Frank Pfenning *)

module type EXTCONDEC =
sig

  module ExtSyn : EXTSYN
  (*! module Paths : PATHS !*)

  type condec				(* constant declaration *)
  val condec : string * ExtSyn.term -> condec	(* id : tm *)
  val blockdec : string * ExtSyn.dec list * ExtSyn.dec list -> condec
  val blockdef : string *  (string list * string) list -> condec
  val condef : string option * ExtSyn.term * ExtSyn.term option -> condec
					(* id : tm = tm | _ : tm = tm *)

end (* module type EXTCONDEC *)

module type RECON_CONDEC =
sig

  (*! module IntSyn : INTSYN !*)
  include EXTCONDEC

  exception Error of string

  val condecToConDec : condec * Paths.location * bool -> IntSyn.ConDec option * Paths.occConDec option
                     (* optional ConDec is absent for anonymous definitions *)
                     (* bool = true means that condec is an abbreviation *)

  val internalInst : IntSyn.ConDec * IntSyn.ConDec * Paths.region -> IntSyn.ConDec

  val externalInst : IntSyn.ConDec * ExtSyn.term * Paths.region -> IntSyn.ConDec
end (* module type RECON_CONDEC *)
