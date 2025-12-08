(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

module type STRICT =
sig
  (*! module IntSyn : INTSYN !*)
  (*! module Paths : PATHS !*)

  exception Error of string
  
  val check : (IntSyn.exp * IntSyn.exp) * Paths.occConDec option -> unit
  val checkType : (int * IntSyn.exp) * Paths.occConDec option -> unit
end;; (* module type STRICT *)
