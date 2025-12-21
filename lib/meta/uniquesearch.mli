(* Basic search engine: Version 1.3*)

(* Author: Carsten Schuermann *)

module type UNIQUESEARCH = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type acctype = IntSyn.exp

  val searchEx :
    int * IntSyn.exp list * (acctype list -> acctype list) -> acctype list
end

(* signature SEARCH *)
