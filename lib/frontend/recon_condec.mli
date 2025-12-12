(* External Syntax for signature entries *)
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature EXTCONDEC =
sig

  structure ExtSyn : EXTSYN
  (*! structure Paths : PATHS !*)

  type condec				(* constant declaration *)
  val condec : string * ExtSyn.term -> condec	(* id : tm *)
  val blockdec : string * ExtSyn.dec list * ExtSyn.dec list -> condec
  val blockdef : string *  (string list * string) list -> condec
  val condef : string option * ExtSyn.term * ExtSyn.term option -> condec
					(* id : tm = tm | _ : tm = tm *)

end (* GEN END SIGNATURE DECLARATION *) (* signature EXTCONDEC *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature RECON_CONDEC =
sig

  (*! structure IntSyn : INTSYN !*)
  include EXTCONDEC

  exception Error of string

  val condecToConDec : condec * Paths.location * bool -> IntSyn.con_dec option * Paths.occ_con_dec option
                     (* optional ConDec is absent for anonymous definitions *)
                     (* bool = true means that condec is an abbreviation *)

  val internalInst : IntSyn.con_dec * IntSyn.con_dec * Paths.region -> IntSyn.con_dec

  val externalInst : IntSyn.con_dec * ExtSyn.term * Paths.region -> IntSyn.con_dec
end (* GEN END SIGNATURE DECLARATION *) (* signature RECON_CONDEC *)
