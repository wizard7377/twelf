(* Converter from relational representation to a functional
   representation of proof terms *)

(* Author: Carsten Schuermann *)

module type CONVERTER = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string
  exception Error' of Tomega.sub

  val convertFor : IntSyn.cid list -> Tomega.for_sml
  val convertPrg : IntSyn.cid list -> Tomega.prg

  val installPrg :
    IntSyn.cid list ->
    IntSyn.cid * Tomega.lemma list (* projections *) * Tomega.lemma list

  (* selections *)
  val convertGoal : Tomega.dec IntSyn.ctx * IntSyn.exp -> Tomega.prg
end

(* Signature CONVERTER *)
