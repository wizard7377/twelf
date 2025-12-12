(* Lemma *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature LEMMA = 
sig
  structure MetaSyn : METASYN
    
  exception Error of string

  val apply : MetaSyn.state * IntSyn.cid -> MetaSyn.state 
end (* GEN END SIGNATURE DECLARATION *);  (* signature LEMMA *)
