(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

signature STATESYN =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)

  datatype order =	       	        (* Orders                     *)
    Arg of (IntSyn.exp * IntSyn.sub) * 
           (IntSyn.exp * IntSyn.sub)	(* O ::= U[s] : V[s]          *)
  | Lex of order list			(*     | (O1 .. On)           *)
  | Simul of order list			(*     | {O1 .. On}           *)
  | All of IntSyn.dec * order  	(*     | {{D}} O              *)
  | And of order * order		(*     | O1 ^ O2              *)


  datatype info =
    Splits of int
  | RL 
  | RLdone
    
  datatype tag = 
    Parameter of FunSyn.label option
  | Lemma of info
  | None

  datatype state =			(* S = <n, (G, B), (IH, OH), d, O, H, F> *)
    State of int			(* Part of theorem                   *)
	   * (IntSyn.dctx	(* Context of Hypothesis, in general not named *)
           * tag IntSyn.ctx) (* Status information *)
           * (FunSyn.for * order)	(* Induction hypothesis, order       *)
           * int			(* length of meta context            *)
           * order			(* Current order *)
           * (int * FunSyn.for) list	(* History of residual lemmas *)
           * FunSyn.for			(* Formula *)

  val orderSub : order * IntSyn.sub -> order  
  val decrease : tag -> tag
  val splitDepth : info -> int

  val normalizeOrder : order -> order
  val convOrder : order * order -> bool

  val normalizeTag : tag * IntSyn.sub -> tag
end; (* signature STATESYN *)