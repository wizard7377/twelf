(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) FunSyn ((*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                structure Conv : CONV
                (*! sharing Conv.IntSyn = IntSyn' !*)
                  ) : FUNSYN =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string


  type label = int
  type name = string
  type lemma = int

  type dlist = IntSyn.dec list

  datatype label_dec =                   (* ContextBody                *)
    LabelDec of name * dlist * dlist
                                        (* BB ::= l: SOME Theta. Phi  *)

  datatype ctx_block =                   (* ContextBlocks              *)
    CtxBlock of
      label option * IntSyn.dctx        (* B ::= l : Phi              *)

  datatype lf_dec =                      (* Contexts                   *)
    Prim of IntSyn.dec                  (* LD ::= x :: A              *)
  | Block of ctx_block                   (*      | B                   *)

  type lfctx = lf_dec IntSyn.ctx         (* Psi ::= . | Psi, LD        *)

  datatype for =                        (* Formulas                   *)
    All of lf_dec * for                  (* F ::= All LD. F            *)
  | Ex  of IntSyn.dec * for             (*     | Ex  D. F             *)
  | True                                (*     | T                    *)
  | And of for * for                    (*     | F1 ^ F2              *)

  datatype pro =                        (* Programs                   *)
    Lam of lf_dec * pro                  (* P ::= lam LD. P            *)
  | Inx of IntSyn.exp * pro             (*     | <M, P>               *)
  | Unit                                (*     | <>                   *)
  | Rec of m_dec * pro                   (*     | mu xx. P             *)
  | Let of decs * pro                   (*     | let Ds in P          *)
  | Case of opts                        (*     | case O               *)
  | Pair of pro * pro                   (*     | <P1, P2>             *)

  and opts =                            (* Option list                *)
    Opts of (lfctx * IntSyn.sub * pro) list
                                        (* O ::= (Psi' |> s |-> P     *)

  and m_dec =                            (* Meta Declaration:          *)
    MDec of name option * for           (* DD ::= xx : F              *)

  and decs =                            (* Declarations               *)
    Empty                               (* Ds ::= .                   *)
  | Split of int * decs                 (*      | <x, yy> = P, Ds     *)
  | New of ctx_block * decs              (*      | nu B. Ds            *)
  | App of (int * IntSyn.exp) * decs    (*      | xx = yy M, Ds       *)
  | PApp of (int * int) * decs          (*      | xx = yy Phi, Ds     *)
  | Lemma of lemma * decs               (*      | xx = cc, Ds         *)
  | Left of int * decs                  (*      | xx = pi1 yy, Ds     *)
  | Right of int * decs                 (*      | xx = pi2 yy, Ds     *)

  datatype lemma_dec =                   (* Lemmas                     *)
    LemmaDec of name list * pro * for   (* L ::= c:F = P              *)

  type mctx = m_dec IntSyn.ctx           (* Delta ::= . | Delta, xx : F*)

  local
    structure I = IntSyn
    (* GEN BEGIN TAG OUTSIDE LET *) val maxLabel = Global.maxCid (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val maxLemma = Global.maxCid (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val labelArray = Array.array (maxLabel+1,
                                  LabelDec("", nil, nil))
                   : label_dec Array.array (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nextLabel = ref 0 (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val lemmaArray = Array.array (maxLemma+1, LemmaDec (nil, Unit, True))
                   : lemma_dec Array.array (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val nextLemma = ref 0 (* GEN END TAG OUTSIDE LET *)

    fun labelLookup label = Array.sub (labelArray, label)
    fun labelAdd (labelDec) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val label = !nextLabel (* GEN END TAG OUTSIDE LET *)
        in
          if label > maxLabel
            then raise Error ("Global signature size " ^ Int.toString (maxLabel+1) ^ " exceeded")
          else (Array.update (labelArray, label, labelDec) ;
                nextLabel := label + 1;
                label)
        end
    fun labelSize () = (!nextLabel)
    fun labelReset () = (nextLabel := 0)


    fun lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    fun lemmaAdd (lemmaDec) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val lemma = !nextLemma (* GEN END TAG OUTSIDE LET *)
        in
          if lemma > maxLemma
            then raise Error ("Global signature size " ^ Int.toString (maxLemma+1) ^ " exceeded")
          else (Array.update (lemmaArray, lemma, lemmaDec) ;
                nextLemma := lemma + 1;
                lemma)
        end
    fun lemmaSize () = (!nextLemma)

(* hack!!! improve !!!! *)
    fun listToCtx (Gin) =
      let
        fun (* GEN BEGIN FUN FIRST *) listToCtx' (G, nil) = G (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) listToCtx' (G, D :: Ds) =
                listToCtx' (I.Decl (G, D), Ds) (* GEN END FUN BRANCH *)
      in
        listToCtx' (I.Null, Gin)
      end

    fun ctxToList (Gin) =
      let
        fun (* GEN BEGIN FUN FIRST *) ctxToList' (I.Null, G ) = G (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) ctxToList' (I.Decl (G, D), G') =
          ctxToList' (G, D :: G') (* GEN END FUN BRANCH *)
      in
        ctxToList' (Gin, nil)
      end


    (* union (G, G') = G''

       Invariant:
       G'' = G, G'
    *)
    fun (* GEN BEGIN FUN FIRST *) union (G, I.Null) = G (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) union (G, I.Decl (G', D)) = I.Decl (union(G, G'), D) (* GEN END FUN BRANCH *)

    (* makectx Psi = G

       Invariant:
       G is Psi, where the Prim/Block information is discarded.
    *)
    fun (* GEN BEGIN FUN FIRST *) makectx (I.Null) = I.Null (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) makectx (I.Decl (G, Prim D)) = I.Decl (makectx G, D) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) makectx (I.Decl (G, Block (CtxBlock (l, G')))) = union (makectx G, G') (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) lfctxLength (I.Null) = 0 (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lfctxLength (I.Decl (Psi, Prim _))= (lfctxLength Psi) + 1 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lfctxLength (I.Decl (Psi, Block (CtxBlock (_, G)))) =
          (lfctxLength Psi) + (I.ctxLength G) (* GEN END FUN BRANCH *)


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
        fun (* GEN BEGIN FUN FIRST *) lfctxLFDec' (I.Decl (Psi', LD as Prim (I.Dec (x, V'))), 1) =
              (LD, I.Shift k) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) lfctxLFDec' (I.Decl (Psi', Prim _), k') = lfctxLFDec' (Psi', k'-1) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) lfctxLFDec' (I.Decl (Psi', LD as Block (CtxBlock (_, G))), k') =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val l = I.ctxLength G (* GEN END TAG OUTSIDE LET *)
            in
              if k' <= l then
                (LD, I.Shift (k - k' + 1))
              else
                lfctxLFDec' (Psi', k' - l)
            end (* GEN END FUN BRANCH *)
    
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
    fun (* GEN BEGIN FUN FIRST *) dot1n (I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) dot1n (I.Decl (G, _) , s) = I.dot1 (dot1n (G, s)) (* GEN END FUN BRANCH *)


    (* conv ((F1, s1), (F2, s2)) = B

       Invariant:
       If   G |- s1 : G1
       and  G1 |- F1 : formula
       and  G |- s2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)

    fun (* GEN BEGIN FUN FIRST *) convFor ((True, _), (True, _)) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convFor ((All (Prim D1, F1), s1),
                 (All (Prim D2, F2), s2)) =
          Conv.convDec ((D1, s1), (D2, s2))
          andalso convFor ((F1, I.dot1 s1), (F2, I.dot1 s2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convFor ((All (Block (CtxBlock ((* SOME l1 *) _, G1)), F1), s1),
                 (All (Block (CtxBlock ((* SOME l2 *) _, G2)), F2), s2)) =
         (* l1 = l2 andalso *) convForBlock ((ctxToList G1, F1, s1), (ctxToList G1, F2, s2)) (* GEN END FUN BRANCH *)
         (* omission! check that the block numbers are the same!!!! *)
      | (* GEN BEGIN FUN BRANCH *) convFor ((Ex (D1, F1), s1),
                 (Ex (D2, F2), s2)) =
          Conv.convDec ((D1, s1), (D2, s2))
          andalso convFor ((F1, I.dot1 s1), (F2, I.dot1 s2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convFor ((And (F1, F1'), s1), (And (F2, F2'), s2)) =
          convFor ((F1, s1), (F2, s2))
          andalso convFor ((F1', s1), (F2', s2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convFor _ = false (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) convForBlock ((nil, F1, s1), (nil, F2, s2)) =
          convFor ((F1, s1), (F2, s2)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) convForBlock ((D1 :: G1, F1, s1), (D2 :: G2, F2, s2)) =
          Conv.convDec ((D1, s1), (D2, s2))
          andalso convForBlock ((G1, F1, I.dot1 s1), (G2, F2, I.dot1 s2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) convForBlock _ = false (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) ctxSub (I.Null, s) = (I.Null, s) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxSub (I.Decl (G, D), s) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = ctxSub (G, s) (* GEN END TAG OUTSIDE LET *)
        in
          (I.Decl (G', I.decSub (D, s')), I.dot1 s)
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) forSub (All (Prim D, F), s) =
          All (Prim (I.decSub (D, s)), forSub (F, I.dot1 s)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) forSub (All (Block (CtxBlock (name, G)), F), s) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (G', s') = ctxSub (G, s) (* GEN END TAG OUTSIDE LET *)
          in
            All (Block (CtxBlock (name, G')), forSub (F, s'))
          end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) forSub (Ex (D, F), s) =
          Ex (I.decSub (D, s), forSub (F, I.dot1 s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) forSub (True, s) = True (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) forSub (And (F1, F2), s) =
          And (forSub (F1, s), forSub (F2, s)) (* GEN END FUN BRANCH *)

    fun mdecSub (MDec (name, F), s) = MDec (name, forSub (F, s))


    fun (* GEN BEGIN FUN FIRST *) normalizeFor (All (Prim D, F), s) =
          All (Prim (Whnf.normalizeDec (D, s)), normalizeFor (F, I.dot1 s)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (Ex (D, F), s) =
          Ex (Whnf.normalizeDec (D, s), normalizeFor (F, I.dot1 s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (And (F1, F2), s) =
          And (normalizeFor (F1, s), normalizeFor (F2, s)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (True, _) = True (* GEN END FUN BRANCH *)



  in
    (* GEN BEGIN TAG OUTSIDE LET *) val labelLookup = labelLookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val labelAdd = labelAdd (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val labelSize = labelSize (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val labelReset = labelReset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lemmaLookup = lemmaLookup (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lemmaAdd = lemmaAdd (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lemmaSize = lemmaSize (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val mdecSub = mdecSub (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val makectx = makectx (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lfctxLength = lfctxLength (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lfctxLFDec = lfctxLFDec (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val dot1n = dot1n (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val convFor = convFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val forSub = forSub (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizeFor = normalizeFor (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val ctxToList = ctxToList (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val listToCtx = listToCtx (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *);  (* functor FunSyn *)

structure FunSyn =
  FunSyn ((*! structure IntSyn' = IntSyn !*)
          structure Whnf = Whnf
          structure Conv = Conv);
