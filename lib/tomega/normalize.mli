(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature NORMALIZE = 
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA

  val normalizeFor : (Tomega.for * Tomega.sub) -> Tomega.for
  val normalizePrg : (Tomega.prg * Tomega.sub) -> Tomega.prg 
  val normalizeSpine : (Tomega.spine * Tomega.sub) -> Tomega.spine 
  val normalizeSub : Tomega.sub -> Tomega.sub 
end (* GEN END SIGNATURE DECLARATION *)
