(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

module type UNIQUESEARCH = 
sig
  (*! module IntSyn : INTSYN !*)
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type acctype = IntSyn.Exp

  val searchEx : int * IntSyn.Exp list
      * (acctype list -> acctype list) -> acctype list
end;  (* module type SEARCH *)
