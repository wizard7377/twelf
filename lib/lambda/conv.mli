(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type CONV =
sig
  (*! module IntSyn : INTSYN !*)

  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val convDec : (IntSyn.Dec * IntSyn.Sub) * (IntSyn.Dec * IntSyn.Sub)-> bool
  val convSub : IntSyn.Sub * IntSyn.Sub -> bool
end;  (* module type CONV *)
