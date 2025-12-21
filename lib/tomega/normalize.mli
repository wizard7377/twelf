(* Normalizer for_sml Delphin meta level *)

(* Author: Carsten Schuermann *)

module type NORMALIZE = sig
  module IntSyn : INTSYN
  module Tomega : TOMEGA

  val normalizeFor : Tomega.for_sml * Tomega.sub -> Tomega.for_sml
  val normalizePrg : Tomega.prg * Tomega.sub -> Tomega.prg
  val normalizeSpine : Tomega.spine * Tomega.sub -> Tomega.spine
  val normalizeSub : Tomega.sub -> Tomega.sub
end
