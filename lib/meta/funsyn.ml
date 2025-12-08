(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

module FunSyn ((*! module IntSyn' : INTSYN !*)
                (Whnf : WHNF)
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                (Conv : CONV): FUNSYN =
                (*! sharing Conv.IntSyn = IntSyn' !*)
struct
  (*! module IntSyn = IntSyn' !*)

  exception Error of string


  type label = int
  type name = string
  type lemma = int

  type dlist = IntSyn.Dec list

  type labelDec =                   (* ContextBody                *)
    LabelDec of name * dlist * dlist
                                        (* BB ::= l: SOME Theta. Phi  *)

  type ctxBlock =                   (* ContextBlocks              *)
    CtxBlock of
      label option * IntSyn.dctx        (* B ::= l : Phi              *)

  type lfDec =                      (* Contexts                   *)
    Prim of IntSyn.Dec                  (* LD ::= x :: A              *)
  | Block of CtxBlock                   (*      | B                   *)

  type lfctx = LFDec IntSyn.ctx         (* Psi ::= . | Psi, LD        *)

  type for =                        (* Formulas                   *)
    All of lfDec * for                  (* F ::= All LD. F            *)
  | Ex  of IntSyn.Dec * for             (*     | Ex  D. F             *)
  | True                                (*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)

  type pro =                        (* Programs                   *)
    Lam of lfDec * pro                  (* P ::= lam LD. P            *)
  | Inx of IntSyn.exp * pro             (*     | <M, P>               *)
  | Unit                                (*     | <>                   *)
  | Rec of MDec * pro                   (*     | mu xx. P             *)
  | Let of Decs * pro                   (*     | let Ds in P          *)
  | Case of Opts                        (*     | case O               *)
  | Pair of pro * pro                   (*     | <P1, P2>             *)

  and Opts =                            (* Option list                *)
    Opts of (lfctx * IntSyn.Sub * Pro) list
                                        (* O ::= (Psi' |> s |-> P     *)

  and MDec =                            (* Meta Declaration:          *)
    MDec of name option * For           (* DD ::= xx : F              *)

  and Decs =                            (* Declarations               *)
    Empty                               (* Ds ::= .                   *)
  | Split of int * Decs                 (*      | <x, yy> = P, Ds     *)
  | New of CtxBlock * Decs              (*      | nu B. Ds            *)
  | App of (int * IntSyn.exp) * Decs    (*      | xx = yy M, Ds       *)
  | PApp of (int * int) * Decs          (*      | xx = yy Phi, Ds     *)
  | Lemma of lemma * Decs               (*      | xx = cc, Ds         *)
  | Left of int * Decs                  (*      | xx = pi1 yy, Ds     *)
  | Right of int * Decs                 (*      | xx = pi2 yy, Ds     *)

  type lemmaDec =                   (* Lemmas                     *)
    LemmaDec of name list * Pro * For   (* L ::= c:F = P              *)

  type mctx = MDec IntSyn.ctx           (* Delta ::= . | Delta, xx : F*)

  local
    module I = IntSyn
    let maxLabel = Global.maxCid
    let maxLemma = Global.maxCid

    let labelArray = Array.array (maxLabel+1,
                                  LabelDec("", nil, nil))
                   : LabelDec Array.array
    let nextLabel = ref 0

    let lemmaArray = Array.array (maxLemma+1, LemmaDec (nil, Unit, True))
                   : LemmaDec Array.array
    let nextLemma = ref 0

    fun labelLookup label = Array.sub (labelArray, label)
    fun labelAdd (labelDec) =
        let
          let label = !nextLabel
        in
          if label > maxLabel
            then raise Error ("Global module type size " ^ Int.toString (maxLabel+1) ^ " exceeded")
          else (Array.update (labelArray, label, labelDec) ;
                nextLabel := label + 1;
                label)
        end
    fun labelSize () = (!nextLabel)
    fun labelReset () = (nextLabel := 0)


    fun lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    fun lemmaAdd (lemmaDec) =
        let
          let lemma = !nextLemma
        in
          if lemma > maxLemma
            then raise Error ("Global module type size " ^ Int.toString (maxLemma+1) ^ " exceeded")
          else (Array.update (lemmaArray, lemma, lemmaDec) ;
                nextLemma := lemma + 1;
                lemma)
        end
    fun lemmaSize () = (!nextLemma)

(* hack!!! improve !!!! *)
    fun listToCtx (Gin) =
      let
        let rec listToCtx' = function (G, nil) -> G
          | (G, D :: Ds) -> 
                listToCtx' (I.Decl (G, D), Ds)
      in
        listToCtx' (I.Null, Gin)
      end

    fun ctxToList (Gin) =
      let
        let rec ctxToList' = function (I.Null, G ) -> G
          | (I.Decl (G, D), G') -> 
          ctxToList' (G, D :: G')
      in
        ctxToList' (Gin, nil)
      end


    (* union (G, G') = G''

       Invariant:
       G'' = G, G'
    *)
    let rec union = function (G, I.Null) -> G
      | (G, I.Decl (G', D)) -> I.Decl (union(G, G'), D)

    (* makectx Psi = G

       Invariant:
       G is Psi, where the Prim/Block information is discarded.
    *)
    let rec makectx = function (I.Null) -> I.Null
      | (I.Decl (G, Prim D)) -> I.Decl (makectx G, D)
      | (I.Decl (G, Block (CtxBlock (l, G')))) -> union (makectx G, G')

    let rec lfctxLength = function (I.Null) -> 0
      | (I.Decl (Psi, Prim _)) -> (lfctxLength Psi) + 1
      | (I.Decl (Psi, Block (CtxBlock (_, G)))) -> 
          (lfctxLength Psi) + (I.ctxLength G)


    (* lfctxDec (Psi, k) = (LD', w')
       Invariant:
       If      |Psi| >= k, where |Psi| is size of Psi,
       and     Psi = Psi1, LD, Psi2
       then    Psi |- k = LD or Psi |- k in LD  (if LD is a contextblock
       then    LD' = LD
       and     Psi |- w' : Psi1, LD\1   (w' is a weakening substitution)
       and     LD\1 is LD if LD is prim, and LD\1 = x:A if LD = G, x:A
   *)
    fun lfctxLFDec (Psi, k) =
      let
        let rec lfctxLFDec' = function (I.Decl (Psi', LD as Prim (I.Dec (x, V'))), 1) -> 
              (LD, I.Shift k)
          | (I.Decl (Psi', Prim _), k') -> lfctxLFDec' (Psi', k'-1)
          | (I.Decl (Psi', LD as Block (CtxBlock (_, G))), k') -> 
            let
              let l = I.ctxLength G
            in
              if k' <= l then
                (LD, I.Shift (k - k' + 1))
              else
                lfctxLFDec' (Psi', k' - l)
            end

         (* lfctxDec' (Null, k')  should not occur by invariant *)
      in
        lfctxLFDec' (Psi, k)
      end

    (* dot1n (G, s) = s'

       Invariant:
       If   G1 |- s : G2
       then G1, G |- s' : G2, G
       where s' = 1.(1.  ...     s) o ^ ) o ^
                        |G|-times
    *)
    let rec dot1n = function (I.Null, s) -> s
      | (I.Decl (G, _) , s) -> I.dot1 (dot1n (G, s))


    (* conv ((F1, s1), (F2, s2)) = B

       Invariant:
       If   G |- s1 : G1
       and  G1 |- F1 : formula
       and  G |- s2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)

    let rec convFor = function ((True, _), (True, _)) -> true
      | convFor ((All (Prim D1, F1), s1),
                 (All (Prim D2, F2), s2)) =
          Conv.convDec ((D1, s1), (D2, s2))
          andalso convFor ((F1, I.dot1 s1), (F2, I.dot1 s2))
      | convFor ((All (Block (CtxBlock ((* SOME l1 *) _, G1)), F1), s1),
                 (All (Block (CtxBlock ((* SOME l2 *) _, G2)), F2), s2)) =
         (* l1 = l2 andalso *) convForBlock ((ctxToList G1, F1, s1), (ctxToList G1, F2, s2))
         (* omission! check that the block numbers are the same!!!! *)
      | convFor ((Ex (D1, F1), s1),
                 (Ex (D2, F2), s2)) =
          Conv.convDec ((D1, s1), (D2, s2))
          andalso convFor ((F1, I.dot1 s1), (F2, I.dot1 s2))
      | ((And (F1, F1'), s1), (And (F2, F2'), s2)) -> 
          convFor ((F1, s1), (F2, s2))
          andalso convFor ((F1', s1), (F2', s2))
      | _ -> false
    and convForBlock ((nil, F1, s1), (nil, F2, s2)) =
          convFor ((F1, s1), (F2, s2))
      | convForBlock ((D1 :: G1, F1, s1), (D2 :: G2, F2, s2)) =
          Conv.convDec ((D1, s1), (D2, s2))
          andalso convForBlock ((G1, F1, I.dot1 s1), (G2, F2, I.dot1 s2))
      | convForBlock _ = false


    let rec ctxSub = function (I.Null, s) -> (I.Null, s)
      | (I.Decl (G, D), s) -> 
        let
          let (G', s') = ctxSub (G, s)
        in
          (I.Decl (G', I.decSub (D, s')), I.dot1 s)
        end

    let rec forSub = function (All (Prim D, F), s) -> 
          All (Prim (I.decSub (D, s)), forSub (F, I.dot1 s))
      | (All (Block (CtxBlock (name, G)), F), s) -> 
          let
            let (G', s') = ctxSub (G, s)
          in
            All (Block (CtxBlock (name, G')), forSub (F, s'))
          end
      | (Ex (D, F), s) -> 
          Ex (I.decSub (D, s), forSub (F, I.dot1 s))
      | (True, s) -> True
      | (And (F1, F2), s) -> 
          And (forSub (F1, s), forSub (F2, s))

    fun mdecSub (MDec (name, F), s) = MDec (name, forSub (F, s))


    let rec normalizeFor = function (All (Prim D, F), s) -> 
          All (Prim (Whnf.normalizeDec (D, s)), normalizeFor (F, I.dot1 s))
      | (Ex (D, F), s) -> 
          Ex (Whnf.normalizeDec (D, s), normalizeFor (F, I.dot1 s))
      | (And (F1, F2), s) -> 
          And (normalizeFor (F1, s), normalizeFor (F2, s))
      | (True, _) -> True



  in
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
end;; (* functor FunSyn *)

module FunSyn =
  FunSyn ((*! module IntSyn' = IntSyn !*)
          module Whnf = Whnf
          module Conv = Conv);
