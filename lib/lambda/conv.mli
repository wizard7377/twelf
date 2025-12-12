(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature CONV =
sig
  (*! structure IntSyn : INTSYN !*)

  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val convDec : (IntSyn.dec * IntSyn.sub) * (IntSyn.dec * IntSyn.sub)-> bool
  val convSub : IntSyn.sub * IntSyn.sub -> bool
end (* GEN END SIGNATURE DECLARATION *);  (* signature CONV *)
