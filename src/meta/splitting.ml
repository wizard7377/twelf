MTPSplitting  MTPGlobal MTPGLOBAL    Global GLOBAL    StateSyn' STATESYN    Heuristic HEURISTIC    MTPAbstract MTPABSTRACT    MTPAbstract StateSyn  StateSyn'   MTPrint MTPRINT    MTPrint StateSyn  StateSyn'   Names NAMES    Conv CONV    Whnf WHNF    TypeCheck TYPECHECK    Subordinate SUBORDINATE    FunTypeCheck FUNTYPECHECK    FunTypeCheck StateSyn  StateSyn'   Index INDEX    Print PRINT    Unify UNIFY     MTPSPLITTING  struct module exception (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for a given operator by applicable)
  *)
type Flagtype Operatortype Operatormodule module module module let rec makeOperator((s,  , k),  , l,  , splits n,  , g,  , i,  , m,  , true) operator ((s,  , k),  , l,  , {sd =  nn; ind =  ii; c =  length llength l; m =  mm; r =  11; p =  g + 1g + 1}) makeOperator((s,  , k),  , l,  , splits n,  , g,  , i,  , m,  , false) operator ((s,  , k),  , l,  , {sd =  nn; ind =  ii; c =  length llength l; m =  mm; r =  00; p =  g + 1g + 1})(* aux (G, B) = L'

       Invariant:
       If   . |- G ctx
       and  G |- B tags
       then . |- L' = GxB lfctx
    *)
let rec aux(null,  , null) null aux(decl (g,  , d),  , decl (b,  , lemma _)) decl (aux (g,  , b),  , prim d) aux(g as decl (_,  , d),  , b as decl (_,  , parameter (sOME l))) let let  inlet  in in decl (psi',  , block (ctxBlock (sOME l,  , g'))) aux'(g,  , b,  , 0) (aux (g,  , b),  , null) aux'(decl (g,  , d),  , decl (b,  , parameter (sOME _)),  , n) let let  in in (psi',  , decl (g',  , d))(* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
let rec conv(gs,  , gs') let exception let rec conv((null,  , s),  , (null,  , s')) (s,  , s') conv((decl (g,  , dec (_,  , v)),  , s),  , (decl (g',  , dec (_,  , v')),  , s')) let let  inlet  in in if conv ((v,  , s1),  , (v',  , s1')) then ps else raise (conv) conv_ raise (conv) in try  with (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
let rec createEVarSpine(g,  , vs) createEVarSpineW (g,  , whnf vs) createEVarSpineW(g,  , vs as (uni type,  , s)) (nil,  , vs) createEVarSpineW(g,  , vs as (root _,  , s)) (nil,  , vs) createEVarSpineW(g,  , (pi ((d as dec (_,  , v1),  , _),  , v2),  , s)) let let  inlet  in in (app (x,  , s),  , vs)(* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomConst(g,  , h) let let  inlet  inlet  in in (root (h,  , s),  , vs)(* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
let rec createAtomBVar(g,  , k) let let  inlet  in in (root (bVar (k),  , s),  , vs)(* someEVars (G, G1, s) = s'

       Invariant:
       If   |- G ctx
       and  G |- s : G'
       then G |- s' : G', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)
let rec someEVars(g,  , nil,  , s) s someEVars(g,  , dec (_,  , v) :: l,  , s) someEVars (g,  , l,  , dot (exp (newEVar (g,  , eClo (v,  , s))),  , s))let rec maxNumberParamsa let let rec maxNumberParams'(n) if n < 0 then 0 else let let  inlet  in in maxNumberParams' (n - 1) + m' in maxNumberParams' (labelSize () - 1)let rec maxNumberLocalParams(pi ((dec (_,  , v1),  , _),  , v2),  , a) let let  in in if targetFam v1 = a then m + 1 else m maxNumberLocalParams(root _,  , a) 0let rec maxNumberConstCasesa length (lookup a)let rec maxNumberCases(v,  , a) maxNumberParams a + maxNumberLocalParams (v,  , a) + maxNumberConstCases a(* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
let rec ctxSub(nil,  , s) nil ctxSub(d :: g,  , s) decSub (d,  , s) :: ctxSub (g,  , dot1 s)let rec createTags(0,  , l) null createTags(n,  , l) decl (createTags (n - 1,  , l),  , parameter (sOME l))let rec createLemmaTags(null) null createLemmaTags(decl (g,  , d)) decl (createLemmaTags g,  , lemma (splits (! maxSplit)))(* constCases (G, (V, s), I, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)
let rec constCases(g,  , vs,  , nil,  , abstract,  , ops) ops constCases(g,  , vs,  , const c :: sgn,  , abstract,  , ops) let let  in in constCases (g,  , vs,  , sgn,  , abstract,  , trail (fun () -> try  with ))(* paramCases (G, (V, s), k, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in G
    *)
let rec paramCases(g,  , vs,  , 0,  , abstract,  , ops) ops paramCases(g,  , vs,  , k,  , abstract,  , ops) let let  in in paramCases (g,  , vs,  , k - 1,  , abstract,  , trail (fun () -> try  with ))let rec constAndParamCasesops0(c,  , g,  , k,  , (v,  , s'),  , abstract) constCases (g,  , (v,  , s'),  , lookup c,  , abstract,  , paramCases (g,  , (v,  , s'),  , k,  , abstract,  , ops0))let rec metaCases(d,  , ops0)(c,  , g,  , k,  , vs,  , abstract) let let  inlet rec select(0,  , ops) ops select(d',  , ops) let let  inlet  inlet  in in select (d' - 1,  , ops') in select (d,  , ops0)(* lowerSplitDest (G, k, (V, s'), abstract) = ops'

       Invariant:
       If  G0, G |- s' : G1  G1 |- V: type
       and  k = |local parameters in G|
       and  G is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
            (it contains constant and parameter cases)
    *)
let rec lowerSplitDest(g,  , k,  , (v as root (const c,  , _),  , s'),  , abstract,  , cases) cases (c,  , g,  , ctxLength g,  , (v,  , s'),  , abstract) lowerSplitDest(g,  , k,  , (pi ((d,  , p),  , v),  , s'),  , abstract,  , cases) let let  in in lowerSplitDest (decl (g,  , d'),  , k + 1,  , (v,  , dot1 s'),  , fun u -> abstract (lam (d',  , u)),  , cases)let rec abstractErrorLeft((g,  , b),  , s) (raise (error "Cannot split left of parameters"))let rec abstractErrorRight((g,  , b),  , s) (raise (error "Cannot split right of parameters"))(* split (x:D, sc, B, abstract) = cases'

       Invariant :
       If   |- G ctx
       and  G |- B tags
       and  G |- D : L
       then sc is a function, which maps
                Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)

       then cases' = (S1, ... Sn) are cases of the split
    *)
let rec split((d as dec (_,  , v),  , t),  , sc,  , abstract) let let rec split'(n,  , cases) if n < 0 then let let  in(* |- G' = parameter blocks of G  ctx*)
(* G' |- B' tags *)
(* G' |- s' : G *)
let rec abstract'u' let (* G' |- U' : V[s'] *)
(* G' |- U'.s' : G, V[s'] *)
let  inlet  in in abstract ((g'',  , b''),  , s'') in lowerSplitDest (g',  , 0,  , (v,  , s'),  , abstract',  , constAndParamCases cases) else let let  inlet  in(* . |- t : G1 *)
let  inlet  in(* . |- G2 [t] ctx *)
let  inlet  in(* G2 [t] |- B2 tags *)
let  in(* . |- G' ctx *)
(* G' |- B' tags *)
(* G' |- s : G = G0 *)
(* G0 |- B0 tags *)
(* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *)
let rec abstract'u' if p then (raise (error "Cannot split right of parameters")) else let (* G' |- U.s' : G, V *)
(* . |- t : G1 *)
let  in(* . |- G'' ctx *)
(* G'' |- B'' tags *)
(* G'' = G1'', G2', G2'' *)
(* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
let  in in abstract ((g'',  , b''),  , s'')let  in in split' (n - 1,  , cases') in split' (labelSize () - 1,  , nil)(* occursInExp (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
let rec occursInExp(k,  , uni _) false occursInExp(k,  , pi (dP,  , v)) occursInDecP (k,  , dP) || occursInExp (k + 1,  , v) occursInExp(k,  , root (c,  , s)) occursInCon (k,  , c) || occursInSpine (k,  , s) occursInExp(k,  , lam (d,  , v)) occursInDec (k,  , d) || occursInExp (k + 1,  , v) occursInExp(k,  , fgnExp csfe) fold csfe (fun (u,  , b) -> b || occursInExp (k,  , normalize (u,  , id))) false(* no case for Redex, EVar, EClo *)
 occursInCon(k,  , bVar (k')) (k = k') occursInCon(k,  , const _) false occursInCon(k,  , def _) false occursInCon(k,  , skonst _) false(* no case for FVar *)
 occursInSpine(_,  , nil) false occursInSpine(k,  , app (u,  , s)) occursInExp (k,  , u) || occursInSpine (k,  , s)(* no case for SClo *)
 occursInDec(k,  , dec (_,  , v)) occursInExp (k,  , v) occursInDecP(k,  , (d,  , _)) occursInDec (k,  , d)let rec isIndexInitk falselet rec isIndexSucc(d,  , isIndex)k occursInDec (k,  , d) || isIndex (k + 1)let rec isIndexFail(d,  , isIndex)k isIndex (k + 1)(* abstractInit S ((G', B'), s') = S'

       Invariant:
       If   |- S = (n, (G, B), (IH, OH), d, O, H, F) state
       and  |- G' ctx
       and  G' |- B' tags
       and  G' |- s' : G
       then |- S' = (n, (G', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
let rec abstractInit(s as state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f))((g',  , b'),  , s') (if ! doubleCheck then typeCheckCtx g' else (); if ! doubleCheck then isFor (g',  , forSub (f,  , s')) else (); state (n,  , (g',  , b'),  , (iH,  , oH),  , d,  , orderSub (o,  , s'),  , map (fun (i,  , f') -> (i,  , forSub (f',  , s'))) h,  , forSub (f,  , s')))(* abstractCont ((x:V, T), abstract) = abstract'

       Invariant:
       If   |- G ctx
       and  G |- V : type
       and  G |- B tags
       and  abstract is an abstraction function which maps
                    (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G, D)
                 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
                    (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : G)
                 to S'               (|- S' state)
    *)
let rec abstractCont((d,  , t),  , abstract)((g,  , b),  , s) abstract ((decl (g,  , normalizeDec (d,  , s)),  , decl (b,  , normalizeTag (t,  , s))),  , dot1 s)let rec makeAddressInitsk (s,  , k)let rec makeAddressContmakeAddressk makeAddress (k + 1)let rec occursInOrder(n,  , arg (us,  , vt),  , k,  , sc) let let  in in if occursInExp (k,  , u') then sOME (n) else sc (n + 1) occursInOrder(n,  , lex os,  , k,  , sc) occursInOrders (n,  , os,  , k,  , sc) occursInOrder(n,  , simul os,  , k,  , sc) occursInOrders (n,  , os,  , k,  , sc)(* no other case should be possible by invariant *)
 occursInOrders(n,  , nil,  , k,  , sc) sc n occursInOrders(n,  , o :: os,  , k,  , sc) occursInOrder (n,  , o,  , k,  , fun n' -> occursInOrders (n',  , os,  , k,  , sc))let rec inductionInitok occursInOrder (0,  , o,  , k,  , fun n -> nONE)let rec inductionContinductionk induction (k + 1)(* expand' ((G, B), isIndex, abstract, makeAddress) = (sc', ops')

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
       and  ops' is a list of splitting operators

       Optimization possible :
         instead of reconstructin (G, B) as the result of sc, just take (G, B)
    *)
let rec expand'(gB as (null,  , null),  , isIndex,  , abstract,  , makeAddress,  , induction) (fun (gp,  , bp) -> ((gp,  , bp),  , shift (ctxLength gp),  , gB,  , false),  , nil) expand'(gB as (decl (g,  , d),  , decl (b,  , t as (lemma (k as splits _)))),  , isIndex,  , abstract,  , makeAddress,  , induction) let let  inlet  inlet rec sc'(gp,  , bp) let let  inlet  in(* G' |- X : V[s'] *)
 in ((g',  , b'),  , dot (exp (x),  , s'),  , (decl (g0,  , d),  , decl (b0,  , t)),  , p')(* G' |- X.s' : G, D *)
let  in in (sc',  , ops') expand'((decl (g,  , d),  , decl (b,  , t as (lemma (rL)))),  , isIndex,  , abstract,  , makeAddress,  , induction) let let  inlet  inlet rec sc'(gp,  , bp) let let  inlet  in in ((g',  , b'),  , dot (exp (x),  , s'),  , (decl (g0,  , d),  , decl (b0,  , t)),  , p') in (sc',  , ops) expand'((decl (g,  , d),  , decl (b,  , t as (lemma (rLdone)))),  , isIndex,  , abstract,  , makeAddress,  , induction) let let  inlet  inlet rec sc'(gp,  , bp) let let  inlet  in in ((g',  , b'),  , dot (exp (x),  , s'),  , (decl (g0,  , d),  , decl (b0,  , t)),  , p') in (sc',  , ops) expand'((decl (g,  , d),  , decl (b,  , t as parameter (sOME _))),  , isIndex,  , abstract,  , makeAddress,  , induction) let let  inlet  inlet rec sc'(gp,  , bp) let let  in in ((decl (g',  , decName (g',  , decSub (d,  , s'))),  , decl (b',  , t)),  , dot1 s',  , (decl (g0,  , d),  , decl (b0,  , t)),  , true) in (sc',  , ops)(* no case of (I.Decl (G, D), I.Decl (G, S.Parameter NONE)) *)
(* expand (S) = ops'

       Invariant:
       If   |- S state
       then ops' is a list of all possiblie splitting operators
    *)
let rec expand(s0 as state (n,  , (g0,  , b0),  , _,  , _,  , o,  , _,  , _)) let let  inlet  in in ops(* index (Op) = k

       Invariant:
       If   Op = (_, Sl)
       then k = |Sl|
    *)
let rec index(operator ((s,  , index),  , sl,  , {c = k; _})) klet rec compare(operator (_,  , _,  , i1),  , operator (_,  , _,  , i2)) compare (i1,  , i2)(* isInActive (F) = B

       Invariant:
       B holds iff F is inactive
    *)
let rec isInActive(active _) false isInActive(inActive) true(* applicable (Op) = B'

       Invariant:
       If   Op = (_, Sl)
       then B' holds iff Sl does not contain inactive states
    *)
let rec applicable(operator (_,  , sl,  , i)) not (exists isInActive sl)(* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
let rec apply(operator (_,  , sl,  , i)) map (fun (active s) -> (if (! doubleCheck) then isState s else (); s) inActive -> raise (error "Not applicable: leftover constraints")) sl(* menu (Op) = s'

       Invariant:
       If   Op = ((S, i), Sl)  and  S is named
       then s' is a string describing the operation in plain text

       (menu should hence be only called on operators which have
        been calculated from a named state)
    *)
let rec menu(op as operator ((state (n,  , (g,  , b),  , (iH,  , oH),  , d,  , o,  , h,  , f),  , i),  , sl,  , i)) let let rec active(nil,  , n) n active(inActive :: l,  , n) active (l,  , n) active((active _) :: l,  , n) active (l,  , n + 1)let rec inactive(nil,  , n) n inactive(inActive :: l,  , n) inactive (l,  , n + 1) inactive((active _) :: l,  , n) inactive (l,  , n)let rec casesToString0 "zero cases" casesToString1 "1 case" casesToStringn (toString n) ^ " cases"let rec flagToString(_,  , 0) "" flagToString(n,  , m) " [active: " ^ (toString n) ^ " inactive: " ^ (toString m) ^ "]" in "Splitting : " ^ decToString (g,  , ctxDec (g,  , i)) ^ " " ^ (indexToString i) ^ (flagToString (active (sl,  , 0),  , inactive (sl,  , 0))) ^ ""let  inlet  inlet  inlet  inlet  inlet  in(* local *)
end