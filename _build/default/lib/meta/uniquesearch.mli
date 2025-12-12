(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature UNIQUESEARCH = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string

  type acctype = IntSyn.exp

  val searchEx : int * IntSyn.exp list
      * (acctype list -> acctype list) -> acctype list
end (* GEN END SIGNATURE DECLARATION *);  (* signature SEARCH *)
