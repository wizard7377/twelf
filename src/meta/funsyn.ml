FunSyn  Whnf WHNF    Conv CONV     FUNSYN  struct (*! structure IntSyn = IntSyn' !*)
exception type Labeltype Nametype Lemmatype Dlisttype LabelDec(* BB ::= l: SOME Theta. Phi  *)
type CtxBlock(* B ::= l : Phi              *)
type LFDec(*      | B                   *)
type Lfctx(* Psi ::= . | Psi, LD        *)
type For(*     | F1 ^ F2              *)
type Pro(*     | <P1, P2>             *)
 Opts(* O ::= (Psi' |> s |-> P     *)
 MDec(* DD ::= xx : F              *)
 Decs(*      | xx = pi2 yy, Ds     *)
type LemmaDec(* L ::= c:F = P              *)
type Mctx(* Delta ::= . | Delta, xx : F*)
module let  inlet  inlet  inlet  inlet  inlet  inlet rec labelLookuplabel sub (labelArray,  , label)let rec labelAdd(labelDec) let let  in in if label > maxLabel then raise (error ("Global signature size " ^ toString (maxLabel + 1) ^ " exceeded")) else (update (labelArray,  , label,  , labelDec); nextLabel := label + 1; label)let rec labelSize() (! nextLabel)let rec labelReset() (nextLabel := 0)let rec lemmaLookuplemma sub (lemmaArray,  , lemma)let rec lemmaAdd(lemmaDec) let let  in in if lemma > maxLemma then raise (error ("Global signature size " ^ toString (maxLemma + 1) ^ " exceeded")) else (update (lemmaArray,  , lemma,  , lemmaDec); nextLemma := lemma + 1; lemma)let rec lemmaSize() (! nextLemma)(* hack!!! improve !!!! *)
let rec listToCtx(gin) let let rec listToCtx'(g,  , nil) g listToCtx'(g,  , d :: ds) listToCtx' (decl (g,  , d),  , ds) in listToCtx' (null,  , gin)let rec ctxToList(gin) let let rec ctxToList'(null,  , g) g ctxToList'(decl (g,  , d),  , g') ctxToList' (g,  , d :: g') in ctxToList' (gin,  , nil)(* union (G, G') = G''

       Invariant:
       G'' = G, G'
    *)
let rec union(g,  , null) g union(g,  , decl (g',  , d)) decl (union (g,  , g'),  , d)(* makectx Psi = G

       Invariant:
       G is Psi, where the Prim/Block information is discarded.
    *)
let rec makectx(null) null makectx(decl (g,  , prim d)) decl (makectx g,  , d) makectx(decl (g,  , block (ctxBlock (l,  , g')))) union (makectx g,  , g')let rec lfctxLength(null) 0 lfctxLength(decl (psi,  , prim _)) (lfctxLength psi) + 1 lfctxLength(decl (psi,  , block (ctxBlock (_,  , g)))) (lfctxLength psi) + (ctxLength g)(* lfctxDec (Psi, k) = (LD', w')
       Invariant:
       If      |Psi| >= k, where |Psi| is size of Psi,
       and     Psi = Psi1, LD, Psi2
       then    Psi |- k = LD or Psi |- k in LD  (if LD is a contextblock
       then    LD' = LD
       and     Psi |- w' : Psi1, LD\1   (w' is a weakening substitution)
       and     LD\1 is LD if LD is prim, and LD\1 = x:A if LD = G, x:A
   *)
let rec lfctxLFDec(psi,  , k) let let rec lfctxLFDec'(decl (psi',  , lD as prim (dec (x,  , v'))),  , 1) (lD,  , shift k) lfctxLFDec'(decl (psi',  , prim _),  , k') lfctxLFDec' (psi',  , k' - 1) lfctxLFDec'(decl (psi',  , lD as block (ctxBlock (_,  , g))),  , k') let let  in in if k' <= l then (lD,  , shift (k - k' + 1)) else lfctxLFDec' (psi',  , k' - l)(* lfctxDec' (Null, k')  should not occur by invariant *)
 in lfctxLFDec' (psi,  , k)(* dot1n (G, s) = s'

       Invariant:
       If   G1 |- s : G2
       then G1, G |- s' : G2, G
       where s' = 1.(1.  ...     s) o ^ ) o ^
                        |G|-times
    *)
let rec dot1n(null,  , s) s dot1n(decl (g,  , _),  , s) dot1 (dot1n (g,  , s))(* conv ((F1, s1), (F2, s2)) = B

       Invariant:
       If   G |- s1 : G1
       and  G1 |- F1 : formula
       and  G |- s2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)
let rec convFor((true,  , _),  , (true,  , _)) true convFor((all (prim d1,  , f1),  , s1),  , (all (prim d2,  , f2),  , s2)) convDec ((d1,  , s1),  , (d2,  , s2)) && convFor ((f1,  , dot1 s1),  , (f2,  , dot1 s2)) convFor((all (block (ctxBlock ((* SOME l1 *)
, _,  , g1)),  , f1),  , s1),  , (all (block (ctxBlock ((* SOME l2 *)
, _,  , g2)),  , f2),  , s2)) convForBlock ((ctxToList g1,  , f1,  , s1),  , (ctxToList g1,  , f2,  , s2)) convFor((ex (d1,  , f1),  , s1),  , (ex (d2,  , f2),  , s2)) convDec ((d1,  , s1),  , (d2,  , s2)) && convFor ((f1,  , dot1 s1),  , (f2,  , dot1 s2)) convFor((and (f1,  , f1'),  , s1),  , (and (f2,  , f2'),  , s2)) convFor ((f1,  , s1),  , (f2,  , s2)) && convFor ((f1',  , s1),  , (f2',  , s2)) convFor_ false convForBlock((nil,  , f1,  , s1),  , (nil,  , f2,  , s2)) convFor ((f1,  , s1),  , (f2,  , s2)) convForBlock((d1 :: g1,  , f1,  , s1),  , (d2 :: g2,  , f2,  , s2)) convDec ((d1,  , s1),  , (d2,  , s2)) && convForBlock ((g1,  , f1,  , dot1 s1),  , (g2,  , f2,  , dot1 s2)) convForBlock_ falselet rec ctxSub(null,  , s) (null,  , s) ctxSub(decl (g,  , d),  , s) let let  in in (decl (g',  , decSub (d,  , s')),  , dot1 s)let rec forSub(all (prim d,  , f),  , s) all (prim (decSub (d,  , s)),  , forSub (f,  , dot1 s)) forSub(all (block (ctxBlock (name,  , g)),  , f),  , s) let let  in in all (block (ctxBlock (name,  , g')),  , forSub (f,  , s')) forSub(ex (d,  , f),  , s) ex (decSub (d,  , s),  , forSub (f,  , dot1 s)) forSub(true,  , s) true forSub(and (f1,  , f2),  , s) and (forSub (f1,  , s),  , forSub (f2,  , s))let rec mdecSub(mDec (name,  , f),  , s) mDec (name,  , forSub (f,  , s))let rec normalizeFor(all (prim d,  , f),  , s) all (prim (normalizeDec (d,  , s)),  , normalizeFor (f,  , dot1 s)) normalizeFor(ex (d,  , f),  , s) ex (normalizeDec (d,  , s),  , normalizeFor (f,  , dot1 s)) normalizeFor(and (f1,  , f2),  , s) and (normalizeFor (f1,  , s),  , normalizeFor (f2,  , s)) normalizeFor(true,  , _) truelet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inend   module