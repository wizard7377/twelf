(* Internal syntax for_sml Delphin *)

(* Author: Carsten Schuermann *)

module type TOMEGA = sig
  (*! structure IntSyn : INTSYN !*)
  (* make abstract *)
  type label = int
  type lemma = int
  type worlds = Worlds of IntSyn.cid list
  type quantifier = Implicit | Explicit

  type tC =
    | Abs of IntSyn.dec * tC
    | Conj of tC * tC
    | Base of (IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub) Order.order

  type for_sml =
    | World of worlds * for_sml
    | All of (dec * quantifier) * for_sml
    | Ex of (IntSyn.dec * quantifier) * for_sml
    | True
    | And of for_sml * for_sml
    | FClo of for_sml * sub
    | FVar of (dec IntSyn.ctx * for_sml option ref)

  and dec =
    | UDec of IntSyn.dec
    | PDec of string option * for_sml * tC option * tC option

  and prg =
    | Box of worlds * prg
    | Lam of dec * prg
    | New of prg
    | Choose of prg
    | PairExp of IntSyn.exp * prg
    | PairBlock of IntSyn.block * prg
    | PairPrg of prg * prg
    | Unit
    | Redex of prg * spine
    | Rec of dec * prg
    | Case of cases
    | PClo of prg * sub
    | Let of dec * prg * prg
    | EVar of
        dec IntSyn.ctx
        * prg option ref
        * for_sml
        * tC option
        * tC option
        * IntSyn.exp
    | Const of lemma
    | Var of int
    | LetPairExp of IntSyn.dec * dec * prg * prg
    | LetUnit of prg * prg

  and spine =
    | Nil
    | AppExp of IntSyn.exp * spine
    | AppBlock of IntSyn.block * spine
    | AppPrg of prg * spine
    | SClo of spine * sub

  and sub = Shift of int | Dot of front * sub

  and front =
    | Idx of int
    | Prg of prg
    | Exp of IntSyn.exp
    | Block of IntSyn.block
    | Undef

  and cases = Cases of dec IntSyn.ctx * sub * prg list

  (* C ::= (Psi' |> s |-> P)    *)
  type conDec = ForDec of string * for_sml | ValDec of string * prg * for_sml

  (*      | f == P              *)
  exception NoMatch

  val coerceSub : sub -> IntSyn.sub
  val embedSub : IntSyn.sub -> sub
  val coerceCtx : dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx
  val strengthenCtx : dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx * sub * sub
  val embedCtx : IntSyn.dec IntSyn.ctx -> dec IntSyn.ctx
  val weakenSub : dec IntSyn.ctx -> sub
  val invertSub : sub -> sub
  val id : sub
  val shift : sub
  val dot1 : sub -> sub
  val dotEta : front * sub -> sub
  val comp : sub * sub -> sub
  val varSub : int * sub -> front
  val decSub : dec * sub -> dec
  val forSub : for_sml * sub -> for_sml
  val whnfFor : for_sml * sub -> for_sml * sub
  val normalizePrg : prg * sub -> prg
  val normalizeSub : sub -> sub
  val derefPrg : prg -> prg
  val lemmaLookup : lemma -> conDec
  val lemmaName : string -> lemma
  val lemmaAdd : conDec -> lemma
  val lemmaSize : unit -> int
  val lemmaDef : lemma -> prg
  val lemmaFor : lemma -> for_sml
  val eqWorlds : worlds * worlds -> bool
  val convFor : (for_sml * sub) * (for_sml * sub) -> bool
  val newEVar : dec IntSyn.ctx * for_sml -> prg
  val newEVarTC : dec IntSyn.ctx * for_sml * tC option * tC option -> prg

  (* Below are added by Yu Liao *)
  val ctxDec : dec IntSyn.ctx * int -> dec
  val revCoerceSub : IntSyn.sub -> sub
  val revCoerceCtx : IntSyn.dec IntSyn.ctx -> dec IntSyn.ctx

  (* Added references by ABP *)
  val coerceFront : front -> IntSyn.front
  val revCoerceFront : IntSyn.front -> front
  val deblockify : IntSyn.dec IntSyn.ctx -> IntSyn.dec IntSyn.ctx * sub

  (* Stuff that has to do with termination conditions *)
  val tCSub : tC * IntSyn.sub -> tC
  val normalizeTC : tC -> tC
  val convTC : tC * tC -> bool
  val transformTC : IntSyn.dec IntSyn.ctx * for_sml * int Order.order list -> tC
end

(* Signature TOMEGA *)
