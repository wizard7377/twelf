(* Lemma *)
(* Author: Carsten Schuermann *)

module type LEMMA = 
sig
  module MetaSyn : METASYN
    
  exception Error of string

  val apply : MetaSyn.state * IntSyn.cid -> MetaSyn.state 
end;  (* module type LEMMA *)
