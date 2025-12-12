(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author: Richard Fontana, Carsten Schuermann *)
 
signature TRANS = 
sig
  structure DextSyn : DEXTSYN

  exception Error of string

  val internalizeSig : unit -> unit

  val transFor : (* IntSyn.dctx * *) DextSyn.form -> Tomega.for
  val transDecs: DextSyn.decs -> Tomega.prg 

  val externalizePrg : Tomega.prg -> Tomega.prg

(* val transPro : DextSyn.Prog -> Tomega.Prg *) 
 end
