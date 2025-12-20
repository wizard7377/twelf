(* State definition for_sml Proof Search *)


(* Author: Carsten Schuermann *)


module type STATESYN = sig
(*! structure IntSyn : INTSYN !*)
(*! structure FunSyn : FUNSYN !*)
  type order = Arg of (IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub) | Lex of order list | Simul of order list | All of IntSyn.dec * order | And of order * order
(*     | O1 ^ O2              *)
  type info = Splits of int | RL | RLdone
  type tag = Parameter of FunSyn.label option | Lemma of info | None
  type state = State of int(* Part of theorem                   *)
 * (IntSyn.dctx(* Context of Hypothesis, in general not named *)
 * tag IntSyn.ctx)(* Status information *)
 * (FunSyn.for_sml * order)(* Induction hypothesis, order       *)
 * int(* length of meta context            *)
 * order(* Current order *)
 * int * FunSyn.for_sml list(* History of residual lemmas *)
 * FunSyn.for_sml
(* Formula *)
  val orderSub : order * IntSyn.sub -> order
  val decrease : tag -> tag
  val splitDepth : info -> int
  val normalizeOrder : order -> order
  val convOrder : order * order -> bool
  val normalizeTag : tag * IntSyn.sub -> tag

end


(* signature STATESYN *)

