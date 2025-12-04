(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type MTPABSTRACT =
sig
  (*! module IntSyn : INTSYN !*)
  (*! module FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type approxFor =			(* Approximat formula *)
    Head of IntSyn.dctx * (FunSyn.For * IntSyn.Sub) * int	(* AF ::= F [s] *)
  | Block of (IntSyn.dctx * IntSyn.Sub * int * IntSyn.Dec list) * approxFor
					(*  | (t, G2), AF *)


  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.Sub
  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp 
      
  val abstractSub : IntSyn.Sub * StateSyn.tag IntSyn.Ctx * (IntSyn.dctx * StateSyn.tag IntSyn.Ctx) * IntSyn.Sub * StateSyn.tag IntSyn.Ctx
        -> ((IntSyn.dctx * StateSyn.tag IntSyn.Ctx) * IntSyn.Sub)
  val abstractSub' : (IntSyn.dctx * StateSyn.tag IntSyn.Ctx) * IntSyn.Sub * StateSyn.tag IntSyn.Ctx
        -> ((IntSyn.dctx * StateSyn.tag IntSyn.Ctx) * IntSyn.Sub)


  val abstractApproxFor : ApproxFor -> FunSyn.for
end;  (* module type MTPABSTRACT *)
