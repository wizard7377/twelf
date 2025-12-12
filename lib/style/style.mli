(* Style Checking *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature STYLECHECK =
sig
  exception Error of string

  val check : unit ->  unit  (* raises Error (msg) *)
  val checkConDec : IntSyn.cid -> unit
end (* GEN END SIGNATURE DECLARATION *);  (* signature STYLECHECK *)
