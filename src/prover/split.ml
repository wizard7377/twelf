Split  Global GLOBAL    State' STATE    Whnf WHNF    Unify UNIFY    Constraints CONSTRAINTS    Abstract ABSTRACT    Index INDEX    Print PRINT    TypeCheck TYPECHECK    Subordinate SUBORDINATE     SPLIT  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
module exception module module module type Operator(* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
let rec weaken(null,  , a) id weaken(decl (g',  , d as dec (name,  , v)),  , a) let let  in in if belowEq (targetFam v,  , a) then dot1 w' else comp (w',  , shift)(* added next case, probably should not arise *)
(* Sun Dec 16 10:42:05 2001 -fp !!! *)
(*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)
(* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
let rec createEVar(g,  , v) let (* G |- V : L *)
let  in(* G  |- w  : G'    *)
let  in(* G' |- iw : G     *)
let  inlet  in(* G' |- X' : V[iw] *)
let  in(* G  |- X  : V     *)
 in x(* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
let rec instEVars(vs,  , p,  , xsRev) instEVarsW (whnf vs,  , p,  , xsRev) instEVarsW(vs,  , 0,  , xsRev) (vs,  , xsRev) instEVarsW((pi ((dec (xOpt,  , v1),  , _),  , v2),  , s),  , p,  , xsRev) let (* p > 0 *)
let  in(* all EVars are global *)
 in instEVars ((v2,  , dot (exp (x1),  , s)),  , p - 1,  , sOME (x1) :: xsRev) instEVarsW((pi ((bDec (_,  , (l,  , t)),  , _),  , v2),  , s),  , p,  , xsRev) let (* p > 0 *)
let  in(* --cs Sun Dec  1 06:33:27 2002 *)
 in instEVars ((v2,  , dot (block (l1),  , s)),  , p - 1,  , nONE :: xsRev)(* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
let  inlet rec resetCases() (caseList := nil)let rec addCase(psi,  , t) (caseList := (psi,  , t) :: ! caseList)let rec getCases() (! caseList)(* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
let rec createEVarSpine(g,  , vs) createEVarSpineW (g,  , whnf vs) createEVarSpineW(g,  , vs as (root _,  , s)) (nil,  , vs) createEVarSpineW(g,  , (pi ((d as dec (_,  , v1),  , _),  , v2),  , s)) let (* G |- V1[s] : L *)
let  inlet  in in (app (x,  , s),  , vs)(* Uni or other cases should be impossible *)
(* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomConst(g,  , h as const (cid)) let let  inlet  in in (root (h,  , s),  , vs)(* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomBVar(g,  , k) let let  inlet  in in (root (bVar (k),  , s),  , vs)(* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomProj(g,  , h,  , (v,  , s)) let let  in in (root (h,  , s),  , vs')let rec constCases(g,  , vs,  , nil,  , sc) () constCases(g,  , vs,  , const (c) :: sgn',  , sc) let let  inlet  in in constCases (g,  , vs,  , sgn',  , sc)let rec paramCases(g,  , vs,  , 0,  , sc) () paramCases(g,  , vs,  , k,  , sc) let let  inlet  in in paramCases (g,  , vs,  , k - 1,  , sc)(* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
let rec createEVarSub(null) id createEVarSub(decl (g',  , d as dec (_,  , v))) let let  inlet  inlet  in in dot (exp x,  , s)(* hack *)
let rec blockName(cid) conDecName (sgnLookup (cid))(* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
let rec blockCases(g,  , vs,  , cid,  , (gsome,  , piDecs),  , sc) let let  in(* accounts for subordination *)
(* . |- t : Gsome *)
let  inlet  inlet  in(* --cs Sun Dec  1 06:33:41 2002 *)
(* G |- t' : Gsome *)
 in blockCases' (g,  , vs,  , (lvar,  , 1),  , (t',  , piDecs),  , sc) blockCases'(g,  , vs,  , (lvar,  , i),  , (t,  , nil),  , sc) () blockCases'(g,  , vs,  , (lvar,  , i),  , (t,  , dec (_,  , v') :: piDecs),  , sc) let (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
(* so G |- V'[t'] : type *)
let  inlet  inlet  in in blockCases' (g,  , vs,  , (lvar,  , i + 1),  , (t',  , piDecs),  , sc)let rec worldCases(g,  , vs,  , worlds (nil),  , sc) () worldCases(g,  , vs,  , worlds (cid :: cids),  , sc) (blockCases (g,  , vs,  , cid,  , constBlock cid,  , sc); worldCases (g,  , vs,  , worlds (cids),  , sc))let rec lowerSplit(g,  , vs,  , w,  , sc) lowerSplitW (g,  , whnf vs,  , w,  , sc) lowerSplitW(g,  , vs as (root (const a,  , _),  , s),  , w,  , sc) let let  in(* will trail *)
let  in(* will trail *)
let  in(* will trail *)
 in ()(*     | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
        end
      we assume that all EVars are lowere :-)
*)
(* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
let rec splitEVar((x as eVar (_,  , gX,  , v,  , _)),  , w,  , sc) lowerSplit (null,  , (v,  , id),  , w,  , fun u -> if unifiable (null,  , (x,  , id),  , (u,  , id)) then sc () else ())(* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)
let rec createSub(null) (id) createSub(decl (psi,  , uDec (dec (xOpt,  , v1)))) let let  inlet  in(* all EVars are global and lowered *)
 in (dot (exp x,  , t')) createSub(decl (psi,  , uDec (bDec (_,  , (l,  , s))))) let let  inlet  in(* --cs Sun Dec  1 06:34:00 2002 *)
 in (dot (block l,  , t')) createSub(decl (psi,  , pDec (_,  , f,  , tC1,  , tC2))) let (* p > 0 *)
let  inlet  in in (dot (prg y,  , t'))(* mkCases L F= Ss

       Invariant:
       If   L is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then Ss is a list of States S1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)
let rec mkCases(nil,  , f) nil mkCases((psi,  , t) :: cs,  , f) let let  in in (psi,  , t,  , x) :: mkCases (cs,  , f)(* split S = S1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for every G |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. G |- t' : Pi
                 and  t = t' [si]
    *)
let rec split(focus (eVar (psi,  , r,  , f,  , nONE,  , nONE,  , _),  , w)) let (* splitXs (G, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  G ~ Psi a context,
           and  G |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
let rec splitXs(g,  , i)(nil,  , _,  , _,  , _) nil splitXs(g,  , i)(x :: xs,  , f,  , w,  , sc) let let  inlet  in(* returns a list of operators *)
let  in(*            val I.Dec (SOME s, _) = I.ctxLookup (G, i) *)
let  inlet  in in os'let  in(* . |- t :: Psi *)
let  inlet rec init() (addCase (abstractTomegaSub t))let  inlet  in in oslet rec expand(s as focus (eVar (psi,  , r,  , f,  , nONE,  , nONE,  , _),  , w)) if closedCTX psi then split s else [](* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
let rec apply(split (r,  , p,  , s)) (r := sOME p)(* trailing required -cs Thu Apr 22 12:05:04 2004 *)
let rec menu(split (_,  , _,  , s)) "Split " ^ stype Operatorlet  inlet  inlet  inend