(* Translator from Delphin external syntax to Delphin internal syntax *)

(* Author: Richard Fontana, Carsten Schuermann *)

module type TRANS = sig
  module DextSyn : DEXTSYN

  exception Error of string

  val internalizeSig : unit -> unit

  val transFor :
    (* IntSyn.dctx * *)
    DextSyn.form ->
    Tomega.for_sml

  val transDecs : DextSyn.decs -> Tomega.prg
  val externalizePrg : Tomega.prg -> Tomega.prg
  (* val transPro : DextSyn.Prog -> Tomega.Prg *)
end
