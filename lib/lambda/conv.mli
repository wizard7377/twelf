(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type CONV =
sig
  (*! module IntSyn : INTSYN !*)

  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val convDec : (IntSyn.dec * IntSyn.Sub) * (IntSyn.dec * IntSyn.Sub)-> bool
  val convSub : IntSyn.Sub * IntSyn.Sub -> bool
end;; (* module type CONV *)
