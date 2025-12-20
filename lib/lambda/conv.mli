(* Convertibility Modulo Beta and Eta *)


(* Author: Frank Pfenning, Carsten Schuermann *)


module type CONV = sig
(*! structure IntSyn : INTSYN !*)
  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val convDec : (IntSyn.dec * IntSyn.sub) * (IntSyn.dec * IntSyn.sub) -> bool
  val convSub : IntSyn.sub * IntSyn.sub -> bool

end


(* signature CONV *)

