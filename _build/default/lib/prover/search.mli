(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature SEARCH = 
sig
  (*! structure IntSyn   : INTSYN !*)
  (*! structure Tomega   : TOMEGA !*)
  structure State    : STATE

  exception Error of string

  val searchEx : int * IntSyn.exp list
(*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
      * (int -> unit) -> unit
end (* GEN END SIGNATURE DECLARATION *);  (* signature SEARCH *)
