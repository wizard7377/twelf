(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type MTPABSTRACT =
sig
  (*! module IntSyn : INTSYN !*)
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type approxfor =			(* Approximat formula *)
    Head of IntSyn.dctx * (FunSyn.For * IntSyn.Sub) * int	(* AF ::= F [s] *)
  | Block of (IntSyn.dctx * IntSyn.Sub * int * IntSyn.dec list) * approxfor
					(*  | (t, G2), AF *)


  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.Sub
  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp 
      
  val abstractSub : IntSyn.Sub * StateSyn.tag IntSyn.ctx * (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.Sub * StateSyn.tag IntSyn.ctx
        -> ((IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.Sub)
  val abstractSub' : (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.Sub * StateSyn.tag IntSyn.ctx
        -> ((IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.Sub)


  val abstractApproxFor : ApproxFor -> FunSyn.for
end;; (* module type MTPABSTRACT *)
