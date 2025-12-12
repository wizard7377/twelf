(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature MTPABSTRACT =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string

  datatype approx_for =			(* Approximat formula *)
    Head of IntSyn.dctx * (FunSyn.for * IntSyn.sub) * int	(* AF ::= F [s] *)
  | Block of (IntSyn.dctx * IntSyn.sub * int * IntSyn.dec list) * approx_for
					(*  | (t, G2), AF *)


  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.sub
  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp 
      
  val abstractSub : IntSyn.sub * StateSyn.tag IntSyn.ctx * (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub * StateSyn.tag IntSyn.ctx
        -> ((IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub)
  val abstractSub' : (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub * StateSyn.tag IntSyn.ctx
        -> ((IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub)


  val abstractApproxFor : approx_for -> FunSyn.for
end;  (* signature MTPABSTRACT *)
