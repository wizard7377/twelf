(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author: Richard Fontana, Carsten Schuermann *)
 
module type TRANS = 
sig
  module DextSyn : DEXTSYN

  exception Error of string

  val internalizeSig : unit -> unit

  val transFor : (* IntSyn.dctx * *) DextSyn.form -> Tomega.For
  val transDecs: DextSyn.decs -> Tomega.Prg 

  val externalizePrg : Tomega.Prg -> Tomega.Prg

(* val transPro : DextSyn.prog -> Tomega.Prg *) 
 end
