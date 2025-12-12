(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)


(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPROVER =
sig
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string 

  val init : FunSyn.for * StateSyn.order -> unit
end (* GEN END SIGNATURE DECLARATION *);  (* signature MTPROVER *)
