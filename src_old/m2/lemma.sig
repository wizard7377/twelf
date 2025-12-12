(* Lemma *)
(* Author: Carsten Schuermann *)

signature LEMMA = 
sig
  structure MetaSyn : METASYN
    
  exception Error of string

  val apply : MetaSyn.state * IntSyn.cid -> MetaSyn.state 
end;  (* signature LEMMA *)
