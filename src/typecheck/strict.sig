(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

signature STRICT =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)

  exception Error of string
  
  val check : (IntSyn.exp * IntSyn.exp) * Paths.occ_con_dec option -> unit
  val checkType : (int * IntSyn.exp) * Paths.occ_con_dec option -> unit
end;  (* signature STRICT *)
