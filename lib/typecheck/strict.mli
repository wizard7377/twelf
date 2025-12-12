(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature STRICT =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)

  exception Error of string
  
  val check : (IntSyn.exp * IntSyn.exp) * Paths.occ_con_dec option -> unit
  val checkType : (int * IntSyn.exp) * Paths.occ_con_dec option -> unit
end (* GEN END SIGNATURE DECLARATION *);  (* signature STRICT *)
