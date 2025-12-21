(* Internal syntax for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

module type FUNSYN = sig
  (*! structure IntSyn : INTSYN !*)
  (* make abstract *)
  type label = int
  type lemma = int
  type labelDec = LabelDec of string * IntSyn.dec list * IntSyn.dec list

  (* BB ::= l: SOME Theta. Phi  *)
  type ctxBlock = CtxBlock of label option * IntSyn.dctx

  (* B ::= l : Phi              *)
  type lFDec = Prim of IntSyn.dec | Block of ctxBlock

  (*      | B                   *)
  (* ??? *)
  type lfctx = lFDec IntSyn.ctx

  (* Psi ::= . | Psi, LD        *)
  type for_sml =
    | All of lFDec * for_sml
    | Ex of IntSyn.dec * for_sml
    | True
    | And of for_sml * for_sml

  (*     | F1 ^ F2              *)
  type pro =
    | Lam of lFDec * pro
    | Inx of IntSyn.exp * pro
    | Unit
    | Rec of mDec * pro
    | Let of decs * pro
    | Case of opts
    | Pair of pro * pro

  and opts = Opts of lfctx * IntSyn.sub * pro list
  and mDec = MDec of string option * for_sml

  and decs =
    | Empty
    | Split of int * decs
    | New of ctxBlock * decs
    | App of (int * IntSyn.exp) * decs
    | PApp of (int * int) * decs
    | Lemma of lemma * decs
    | Left of int * decs
    | Right of int * decs

  (*      | xx = pi2 yy, Ds     *)
  type lemmaDec = LemmaDec of string list * pro * for_sml

  (* L ::= c:F = P              *)
  (* ??? *)
  type mctx = mDec IntSyn.ctx

  (* Delta ::= . | Delta, xx : F*)
  val labelLookup : label -> labelDec
  val labelAdd : labelDec -> label
  val labelSize : unit -> int
  val labelReset : unit -> unit
  val lemmaLookup : lemma -> lemmaDec
  val lemmaAdd : lemmaDec -> lemma
  val lemmaSize : unit -> int
  val mdecSub : mDec * IntSyn.sub -> mDec
  val makectx : lfctx -> IntSyn.dctx
  val lfctxLength : lfctx -> int
  val lfctxLFDec : lfctx * int -> lFDec * IntSyn.sub
  val dot1n : IntSyn.dctx * IntSyn.sub -> IntSyn.sub
  val convFor : (for_sml * IntSyn.sub) * (for_sml * IntSyn.sub) -> bool
  val forSub : for_sml * IntSyn.sub -> for_sml
  val normalizeFor : for_sml * IntSyn.sub -> for_sml
  val listToCtx : IntSyn.dec list -> IntSyn.dctx
  val ctxToList : IntSyn.dctx -> IntSyn.dec list
end

(* Signature FUNSYN *)
