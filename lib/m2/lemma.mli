(* Lemma *)
(* Author: Carsten Schuermann *)

module type LEMMA = 
sig
  module MetaSyn : METASYN
    
  exception Error of string

  val apply : MetaSyn.State * IntSyn.cid -> MetaSyn.State 
end;  (* module type LEMMA *)
