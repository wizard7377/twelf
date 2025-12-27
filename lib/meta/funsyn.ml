open Basis

(* Internal syntax for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

module type FUNSYN = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
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
(* Internal syntax for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

module FunSyn (Whnf : Whnf.WHNF) (Conv : Conv.CONV) : FUNSYN = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  type label = int
  type name = string
  type lemma = int
  type dlist = IntSyn.dec list
  type labelDec = LabelDec of name * dlist * dlist
  (* BB ::= l: SOME Theta. Phi  *)

  type ctxBlock = CtxBlock of label option * IntSyn.dctx
  (* B ::= l : Phi              *)

  type lFDec = Prim of IntSyn.dec | Block of ctxBlock
  (*      | B                   *)

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
  and mDec = MDec of name option * for_sml

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

  type lemmaDec = LemmaDec of name list * pro * for_sml
  (* L ::= c:F = P              *)

  type mctx = mDec IntSyn.ctx
  (* Delta ::= . | Delta, xx : F*)

  module I = IntSyn

  let maxLabel = Global.maxCid
  let maxLemma = Global.maxCid

  let labelArray =
    (Array.array (maxLabel + 1, LabelDec ("", [], [])) : labelDec Array.array)

  let nextLabel = ref 0

  let lemmaArray =
    (Array.array (maxLemma + 1, LemmaDec ([], Unit, True))
      : lemmaDec Array.array)

  let nextLemma = ref 0
  let rec labelLookup label = Array.sub (labelArray, label)

  let rec labelAdd labelDec =
    let label = !nextLabel in
    if label > maxLabel then
      raise
        (Error
           ("Global signature size " ^ Int.toString (maxLabel + 1) ^ " exceeded"))
    else (
      Array.update (labelArray, label, labelDec);
      nextLabel := label + 1;
      label)

  let rec labelSize () = !nextLabel
  let rec labelReset () = nextLabel := 0
  let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)

  let rec lemmaAdd lemmaDec =
    let lemma = !nextLemma in
    if lemma > maxLemma then
      raise
        (Error
           ("Global signature size " ^ Int.toString (maxLemma + 1) ^ " exceeded"))
    else (
      Array.update (lemmaArray, lemma, lemmaDec);
      nextLemma := lemma + 1;
      lemma)

  let rec lemmaSize () = !nextLemma
  (* hack!!! improve !!!! *)

  let rec listToCtx Gin =
    let rec listToCtx' = function
      | G, [] -> G
      | G, D :: Ds -> listToCtx' (I.Decl (G, D), Ds)
    in
    listToCtx' (I.Null, Gin)

  let rec ctxToList Gin =
    let rec ctxToList' = function
      | I.Null, G -> G
      | I.Decl (G, D), G' -> ctxToList' (G, D :: G')
    in
    ctxToList' (Gin, [])
  (* union (G, G') = G''

       Invariant:
       G'' = G, G'
    *)

  let rec union = function
    | G, I.Null -> G
    | G, I.Decl (G', D) -> I.Decl (union (G, G'), D)
  (* makectx Psi = G

       Invariant:
       G is Psi, where the Prim/Block information is discarded.
    *)

  let rec makectx = function
    | I.Null -> I.Null
    | I.Decl (G, Prim D) -> I.Decl (makectx G, D)
    | I.Decl (G, Block (CtxBlock (l, G'))) -> union (makectx G, G')

  let rec lfctxLength = function
    | I.Null -> 0
    | I.Decl (Psi, Prim _) -> lfctxLength Psi + 1
    | I.Decl (Psi, Block (CtxBlock (_, G))) -> lfctxLength Psi + I.ctxLength G
  (* lfctxDec (Psi, k) = (LD', w')
       Invariant:
       If      |Psi| >= k, where |Psi| is size of Psi,
       and     Psi = Psi1, LD, Psi2
       then    Psi |- k = LD or Psi |- k in LD  (if LD is a contextblock
       then    LD' = LD
       and     Psi |- w' : Psi1, LD\1   (w' is a weakening substitution)
       and     LD\1 is LD if LD is prim, and LD\1 = x:A if LD = G, x:A
   *)

  let rec lfctxLFDec (Psi, k) =
    (* lfctxDec' (Null, k')  should not occur by invariant *)
    let rec lfctxLFDec' = function
      | I.Decl (Psi', LD), 1 -> (LD, I.Shift k)
      | I.Decl (Psi', Prim _), k' -> lfctxLFDec' (Psi', k' - 1)
      | I.Decl (Psi', LD), k' ->
          let l = I.ctxLength G in
          if k' <= l then (LD, I.Shift (k - k' + 1))
          else lfctxLFDec' (Psi', k' - l)
    in
    lfctxLFDec' (Psi, k)
  (* dot1n (G, s) = s'

       Invariant:
       If   G1 |- s : G2
       then G1, G |- s' : G2, G
       where s' = 1.(1.  ...     s) o ^ ) o ^
                        |G|-times
    *)

  let rec dot1n = function
    | I.Null, s -> s
    | I.Decl (G, _), s -> I.dot1 (dot1n (G, s))
  (* conv ((F1, s1), (F2, s2)) = B

       Invariant:
       If   G |- s1 : G1
       and  G1 |- F1 : formula
       and  G |- s2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)

  let rec convFor = function
    | (True, _), (True, _) -> true
    | (All (Prim D1, F1), s1), (All (Prim D2, F2), s2) ->
        Conv.convDec ((D1, s1), (D2, s2))
        && convFor ((F1, I.dot1 s1), (F2, I.dot1 s2))
    | ( ( All
            ( Block
                (CtxBlock
                   ( (* SOME l1 *)
                     _,
                     G1 )),
              F1 ),
          s1 ),
        ( All
            ( Block
                (CtxBlock
                   ( (* SOME l2 *)
                     _,
                     G2 )),
              F2 ),
          s2 ) ) ->
        convForBlock ((ctxToList G1, F1, s1), (ctxToList G1, F2, s2))
    | (Ex (D1, F1), s1), (Ex (D2, F2), s2) ->
        Conv.convDec ((D1, s1), (D2, s2))
        && convFor ((F1, I.dot1 s1), (F2, I.dot1 s2))
    | (And (F1, F1'), s1), (And (F2, F2'), s2) ->
        convFor ((F1, s1), (F2, s2)) && convFor ((F1', s1), (F2', s2))
    | _ -> false

  and convForBlock = function
    | ([], F1, s1), ([], F2, s2) -> convFor ((F1, s1), (F2, s2))
    | (D1 :: G1, F1, s1), (D2 :: G2, F2, s2) ->
        Conv.convDec ((D1, s1), (D2, s2))
        && convForBlock ((G1, F1, I.dot1 s1), (G2, F2, I.dot1 s2))
    | _ -> false

  let rec ctxSub = function
    | I.Null, s -> (I.Null, s)
    | I.Decl (G, D), s ->
        let G', s' = ctxSub (G, s) in
        (I.Decl (G', I.decSub (D, s')), I.dot1 s)

  let rec forSub = function
    | All (Prim D, F), s -> All (Prim (I.decSub (D, s)), forSub (F, I.dot1 s))
    | All (Block (CtxBlock (name, G)), F), s ->
        let G', s' = ctxSub (G, s) in
        All (Block (CtxBlock (name, G')), forSub (F, s'))
    | Ex (D, F), s -> Ex (I.decSub (D, s), forSub (F, I.dot1 s))
    | True, s -> True
    | And (F1, F2), s -> And (forSub (F1, s), forSub (F2, s))

  let rec mdecSub (MDec (name, F), s) = MDec (name, forSub (F, s))

  let rec normalizeFor = function
    | All (Prim D, F), s ->
        All (Prim (Whnf.normalizeDec (D, s)), normalizeFor (F, I.dot1 s))
    | Ex (D, F), s -> Ex (Whnf.normalizeDec (D, s), normalizeFor (F, I.dot1 s))
    | And (F1, F2), s -> And (normalizeFor (F1, s), normalizeFor (F2, s))
    | True, _ -> True

  let labelLookup = labelLookup
  let labelAdd = labelAdd
  let labelSize = labelSize
  let labelReset = labelReset
  let lemmaLookup = lemmaLookup
  let lemmaAdd = lemmaAdd
  let lemmaSize = lemmaSize
  let mdecSub = mdecSub
  let makectx = makectx
  let lfctxLength = lfctxLength
  let lfctxLFDec = lfctxLFDec
  let dot1n = dot1n
  let convFor = convFor
  let forSub = forSub
  let normalizeFor = normalizeFor
  let ctxToList = ctxToList
  let listToCtx = listToCtx
end

(* functor FunSyn *)

module FunSyn =
  FunSyn
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Conv = Conv
    end)
