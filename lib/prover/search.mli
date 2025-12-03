(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

module type SEARCH = 
sig
  (*! module IntSyn   : INTSYN !*)
  (*! module Tomega   : TOMEGA !*)
  module State    : STATE

  exception Error of string

  val searchEx : int * IntSyn.Exp list
(*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
      * (int -> unit) -> unit
end;  (* module type SEARCH *)
