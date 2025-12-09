(* Type Checking *)
(* Author: Carsten Schuermann *)

module type TYPECHECK =
sig
  (*! module IntSyn : INTSYN !*)

    exception Error of string

    val check : IntSyn.exp * IntSyn.exp  -> unit
    val checkDec : IntSyn.dctx * (IntSyn.dec * IntSyn.Sub) -> unit 
    val checkConv : IntSyn.exp * IntSyn.exp -> unit
    val infer : IntSyn.exp -> IntSyn.exp
    val infer' : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
    val typeCheck : IntSyn.dctx * (IntSyn.exp * IntSyn.exp) -> unit
    val typeCheckCtx : IntSyn.dctx -> unit
    (* val typeCheckSpine : IntSyn.dctx * IntSyn.Spine -> unit *)
    val typeCheckSub : IntSyn.dctx * IntSyn.Sub * IntSyn.dctx -> unit
end;; (* module type TYPECHECK *)
