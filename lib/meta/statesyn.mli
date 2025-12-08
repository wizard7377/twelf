(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

module type STATESYN =
sig
  (*! module IntSyn : INTSYN !*)
  (*! module FunSyn : FUNSYN !*)

  type order =	       	        (* Orders                     *)
    Arg of (IntSyn.exp * IntSyn.Sub) * 
           (IntSyn.exp * IntSyn.Sub)	(* O ::= U[s] : V[s]          *)
  | Lex of order list			(*     | (O1 .. On)           *)
  | Simul of order list			(*     | {O1 .. On}           *)
  | All of IntSyn.Dec * order  	(*     | {{D}} O              *)
  | And of order * order		(*     | O1 ^ O2              *)


  type info =
    Splits of int
  | RL 
  | RLdone
    
  type tag = 
    Parameter of FunSyn.label option
  | Lemma of Info
  | None

  type state =			(* S = <n, (G, B), (IH, OH), d, O, H, F> *)
    State of int			(* Part of theorem                   *)
	   * (IntSyn.dctx	(* Context of Hypothesis, in general not named *)
           * Tag IntSyn.ctx) (* Status information *)
           * (FunSyn.For * Order)	(* Induction hypothesis, order       *)
           * int			(* length of meta context            *)
           * Order			(* Current order *)
           * (int * FunSyn.For) list	(* History of residual lemmas *)
           * FunSyn.For			(* Formula *)

  val orderSub : order * IntSyn.Sub -> order  
  val decrease : Tag -> Tag
  val splitDepth : Info -> int

  val normalizeOrder : order -> order
  val convOrder : order * order -> bool

  val normalizeTag : tag * IntSyn.Sub -> tag
end;; (* module type STATESYN *)