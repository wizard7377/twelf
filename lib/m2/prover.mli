(* Meta Prover *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PROVER =
sig
  (*! structure IntSyn : INTSYN !*)

  exception Error of string 

  val init   : (int * IntSyn.cid list) -> unit
  val auto   : unit -> unit
  val print  : unit -> unit
  val install: (IntSyn.con_dec -> IntSyn.cid) -> unit
end (* GEN END SIGNATURE DECLARATION *);  (* signature PROVER *)
