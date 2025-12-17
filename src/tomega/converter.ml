Converter  Global GLOBAL    Abstract ABSTRACT    ModeTable MODETABLE    Names NAMES    Unify UNIFY    Whnf WHNF    Print PRINT    TomegaPrint TOMEGAPRINT    WorldSyn WORLDSYN    Worldify WORLDIFY    TomegaTypeCheck TOMEGATYPECHECK    Subordinate SUBORDINATE    TypeCheck TYPECHECK    Redundant REDUNDANT    TomegaAbstract TOMEGAABSTRACT     CONVERTER  struct (*! structure IntSyn = IntSyn' !*)
(*! structure Tomega = Tomega' !*)
exception exception module module module module module module (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)
let rec isIdx1(idx 1) true isIdx1_ falselet rec modeSpinea match modeLookup a with nONE -> raise (error "Mode declaration expected") sOME mS -> mSlet rec typeOfa match sgnLookup a with conDec (name,  , _,  , _,  , _,  , v,  , kind) -> v _ -> raise (error "Type Constant declaration expected")let rec nameOfa match sgnLookup a with conDec (name,  , _,  , _,  , _,  , v,  , kind) -> name _ -> raise (error "Type Constant declaration expected")let rec chatterchlevf if ! chatter >= chlev then print ("[tomega] " ^ f ()) else ()(* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
let rec strengthenExp(u,  , s) normalize (cloInv (u,  , s),  , id)let rec strengthenSub(s,  , t) compInv (s,  , t)(* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
let rec strengthenDec(dec (name,  , v),  , s) dec (name,  , strengthenExp (v,  , s)) strengthenDec(bDec (name,  , (l,  , t)),  , s) bDec (name,  , (l,  , strengthenSub (t,  , s)))(* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- w : G1
       then G1 |- G' = G[w^-1] ctx
       and  G0 |- w' : G1, G'
    *)
let rec strengthenCtx(null,  , s) (null,  , s) strengthenCtx(decl (g,  , d),  , s) let let  in in (decl (g',  , strengthenDec (d,  , s')),  , dot1 s')(* strengthenFor (F, s) = F'

       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1
       then Psi1 |- F' = F[s^-1] ctx
    *)
let rec strengthenFor(true,  , s) true strengthenFor(and (f1,  , f2),  , s) and (strengthenFor (f1,  , s),  , strengthenFor (f2,  , s)) strengthenFor(all ((uDec d,  , q),  , f),  , s) all ((uDec (strengthenDec (d,  , s)),  , q),  , strengthenFor (f,  , dot1 s)) strengthenFor(ex ((d,  , q),  , f),  , s) ex ((strengthenDec (d,  , s),  , q),  , strengthenFor (f,  , dot1 s))(* strengthenOrder (O, s) = O'

       If   Psi0 |- O order
       and  Psi0 |- s :: Psi1
       then Psi1 |- O' = O[s^-1] ctx
    *)
let rec strengthenOrder(arg ((u,  , s1),  , (v,  , s2)),  , s) arg ((u,  , strengthenSub (s1,  , s)),  , (v,  , strengthenSub (s2,  , s))) strengthenOrder(simul os,  , s) simul (map (fun o -> strengthenOrder (o,  , s)) os) strengthenOrder(lex os,  , s) lex (map (fun o -> strengthenOrder (o,  , s)) os)(* strengthenTC (TC, s) = TC'

       If   Psi0 |- TC : termination condition
       and  Psi0 |- s :: Psi1
       then Psi1 |- TC' = TC[s^-1] ctx
    *)
let rec strengthenTC(base o,  , s) base (strengthenOrder (o,  , s)) strengthenTC(conj (tC1,  , tC2),  , s) conj (strengthenTC (tC1,  , s),  , strengthenTC (tC2,  , s)) strengthenTC(abs (d,  , tC),  , s) abs (strengthenDec (d,  , s),  , strengthenTC (tC,  , dot1 s))let rec strengthenSpine(nil,  , t) nil strengthenSpine(app (u,  , s),  , t) app (strengthenExp (u,  , t),  , strengthenSpine (s,  , t))(* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'
    *)
let rec strengthenPsi(null,  , s) (null,  , s) strengthenPsi(decl (psi,  , uDec d),  , s) let let  in in (decl (psi',  , uDec (strengthenDec (d,  , s'))),  , dot1 s') strengthenPsi(decl (psi,  , pDec (name,  , f,  , nONE,  , nONE)),  , s) let let  in in (decl (psi',  , pDec (name,  , strengthenFor (f,  , s'),  , nONE,  , nONE)),  , dot1 s')(* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
let rec strengthenPsi'(nil,  , s) (nil,  , s) strengthenPsi'(uDec d :: psi,  , s) let let  inlet  inlet  in in (uDec d' :: psi'',  , s'')(* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
let rec ctxSub(null,  , s) (null,  , s) ctxSub(decl (g,  , d),  , s) let let  in in (decl (g',  , decSub (d,  , s')),  , dot1 s)let rec validMode(mnil) () validMode(mapp (marg (plus,  , _),  , mS)) validMode mS validMode(mapp (marg (minus,  , _),  , mS)) validMode mS validMode(mapp (marg (star,  , _),  , mS)) raise (error "+ or - mode expected, * found")let rec validSig(psi0,  , nil) () validSig(psi0,  , (g,  , v) :: sig) let let rec append(g,  , null) g append(g,  , decl (g',  , d)) decl (append (g,  , g'),  , d) in (typeCheck (coerceCtx (append (psi0,  , embedCtx g)),  , (v,  , uni type)); validSig (psi0,  , sig))let rec convertOneForcid let let  inlet  inlet  in(* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
let rec convertFor'(pi ((d,  , _),  , v),  , mapp (marg (plus,  , _),  , mS),  , w1,  , w2,  , n) let let  in in (fun f -> all ((uDec (strengthenDec (d,  , w1)),  , explicit),  , f' f),  , f'') convertFor'(pi ((d,  , _),  , v),  , mapp (marg (minus,  , _),  , mS),  , w1,  , w2,  , n) let let  in in (f',  , ex ((decSub (d,  , w2),  , explicit),  , f'')) convertFor'(uni type,  , mnil,  , _,  , _,  , _) (fun f -> f,  , true) convertFor'_ raise (error "type family must be +/- moded")(* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
let rec shiftPlusmS let let rec shiftPlus'(mnil,  , n) n shiftPlus'(mapp (marg (plus,  , _),  , mS'),  , n) shiftPlus' (mS',  , n + 1) shiftPlus'(mapp (marg (minus,  , _),  , mS'),  , n) shiftPlus' (mS',  , n) in shiftPlus' (mS,  , 0)let  inlet  in in f f'(* createIH L = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals
            that corresponds to each type family in L
       and  Psi' |- P' in F'
    *)
let rec createIHnil raise (error "Empty theorem") createIH[a] let let  inlet  in in (name,  , f) createIH(a :: l) let let  inlet  inlet  in in (name ^ "/" ^ name',  , and (f,  , f'))let rec convertForl let let  in in f'(* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
let rec occursInExpN(k,  , uni _) false occursInExpN(k,  , pi (dP,  , v)) occursInDecP (k,  , dP) || occursInExpN (k + 1,  , v) occursInExpN(k,  , root (h,  , s)) occursInHead (k,  , h) || occursInSpine (k,  , s) occursInExpN(k,  , lam (d,  , v)) occursInDec (k,  , d) || occursInExpN (k + 1,  , v) occursInExpN(k,  , fgnExp csfe) fold csfe (fun (u,  , dP) -> dP || (occursInExp (k,  , normalize (u,  , id)))) false(* no case for Redex, EVar, EClo *)
 occursInHead(k,  , bVar (k')) (k = k') occursInHead(k,  , const _) false occursInHead(k,  , def _) false occursInHead(k,  , fgnConst _) false occursInHead(k,  , proj _) false(* no case for FVar *)
 occursInSpine(_,  , nil) false occursInSpine(k,  , app (u,  , s)) occursInExpN (k,  , u) || occursInSpine (k,  , s)(* no case for SClo *)
 occursInDec(k,  , dec (_,  , v)) occursInExpN (k,  , v) occursInDecP(k,  , (d,  , _)) occursInDec (k,  , d) occursInExp(k,  , u) occursInExpN (k,  , normalize (u,  , id))(* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *)
let rec dot1inv(w) strengthenSub (comp (shift,  , w),  , shift)(* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)
let rec shiftinv(w) strengthenSub (w,  , shift)let rec peelw if isIdx1 (bvarSub (1,  , w)) then dot1inv w else shiftinv wlet rec peeln(0,  , w) w peeln(n,  , w) peeln (n - 1,  , peel w)let rec popn(0,  , psi) (psi,  , null) popn(n,  , decl (psi,  , uDec d)) let let  in in (psi',  , decl (g',  , d))(* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
let rec domain(g,  , dot (idx _,  , s)) domain (g,  , s) + 1 domain(null,  , shift 0) 0 domain(g as decl _,  , shift 0) domain (g,  , dot (idx 1,  , shift 1)) domain(decl (g,  , _),  , shift n) domain (g,  , shift (n - 1))(* strengthen (Psi, (a, S), w, m) = (Psi', w')

       This function traverses the spine, and finds
       all variables in a position input/output position m
       (hence strenghten might not be a good name for it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)
let rec strengthen(psi,  , (a,  , s),  , w,  , m) let let  inlet rec args(nil,  , mnil) nil args(app (u,  , s'),  , mapp (marg (m',  , _),  , mS)) let let  in in (match modeEqual (m,  , m') with true -> u :: l false -> l)let rec strengthenArgs(nil,  , s) nil strengthenArgs(u :: l,  , s) strengthenExp (u,  , s) :: strengthenArgs (l,  , s)let rec occursInArgs(n,  , nil) false occursInArgs(n,  , u :: l) (occursInExp (n,  , u) || occursInArgs (n,  , l))let rec occursInPsi(n,  , (nil,  , l)) occursInArgs (n,  , l) occursInPsi(n,  , (uDec (dec (_,  , v)) :: psi1,  , l)) occursInExp (n,  , v) || occursInPsi (n + 1,  , (psi1,  , l)) occursInPsi(n,  , (uDec (bDec (_,  , (cid,  , s))) :: psi1,  , l)) let let  in in occursInSub (n,  , s,  , g) || occursInPsi (n + 1,  , (psi1,  , l)) occursInSub(_,  , _,  , null) false occursInSub(n,  , shift k,  , g) occursInSub (n,  , dot (idx (k + 1),  , shift (k + 1)),  , g) occursInSub(n,  , dot (idx k,  , s),  , decl (g,  , _)) (n = k) || occursInSub (n,  , s,  , g) occursInSub(n,  , dot (exp u,  , s),  , decl (g,  , _)) occursInExp (n,  , u) || occursInSub (n,  , s,  , g) occursInSub(n,  , dot (block _,  , s),  , decl (g,  , _)) occursInSub (n,  , s,  , g)(* is this ok? -- cs *)
(* no other cases *)
 occursInG(n,  , null,  , k) k n occursInG(n,  , decl (g,  , dec (_,  , v)),  , k) occursInG (n,  , g,  , fun n' -> occursInExp (n',  , v) || k (n' + 1))let rec occursBlock(g,  , (psi2,  , l)) let let rec occursBlock(null,  , n) false occursBlock(decl (g,  , d),  , n) occursInPsi (n,  , (psi2,  , l)) || occursBlock (g,  , n + 1) in occursBlock (g,  , 1)(* testBlock (G, (bw, w1)) = (bw', w')

           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
let rec inBlock(null,  , (bw,  , w1)) (bw,  , w1) inBlock(decl (g,  , d),  , (bw,  , w1)) if isIdx1 (bvarSub (1,  , w1)) then inBlock (g,  , (true,  , dot1inv w1)) else inBlock (g,  , (bw,  , strengthenSub (w1,  , shift)))let rec blockSub(null,  , w) (null,  , w) blockSub(decl (g,  , dec (name,  , v)),  , w) let let  inlet  in in (decl (g',  , dec (name,  , v')),  , dot1 w')(* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *)
let rec strengthen'(null,  , psi2,  , l,  , w1, (* =  I.id *)
) (null,  , id,  , id) strengthen'(decl (psi1,  , lD as uDec (dec (name,  , v))),  , psi2,  , l,  , w1) if isIdx1 (bvarSub (1,  , w1)) then let let  inlet  inlet  in in (decl (psi1',  , uDec (dec (name,  , v'))),  , dot1 w',  , dot1 z') else if occursInPsi (1,  , (psi2,  , l)) then let let  inlet  inlet  in in (decl (psi1',  , uDec (dec (name,  , v'))),  , dot1 w',  , comp (z',  , shift)) else let let  inlet  inlet  inlet  inlet  in in (psi1'',  , comp (w',  , shift),  , z') strengthen'(decl (psi1,  , d as pDec (name,  , f,  , nONE,  , nONE)),  , psi2,  , l,  , w1) let let  inlet  inlet  in in (decl (psi1',  , pDec (name,  , f',  , nONE,  , nONE)),  , dot1 w',  , dot1 z') strengthen'(decl (psi1,  , lD as uDec (bDec (name,  , (cid,  , s)))),  , psi2,  , l,  , w1) let (* blocks are always used! *)
let  inlet  inlet  in in (decl (psi1',  , uDec (bDec (name,  , (cid,  , s')))),  , dot1 w',  , dot1 z') in strengthen' (psi,  , nil,  , args (s,  , mS),  , w)let rec lookupIH(psi,  , l,  , a) let let rec lookupIH'(b :: l,  , a,  , k) if a = b then k else lookupIH' (l,  , a,  , k - 1) in lookupIH' (l,  , a,  , ctxLength psi)(* createSub (Psi, L) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
let rec createIHSub(psi,  , l) shift (ctxLength psi - 1(*List.length L *)
)(* transformInit (Psi, (a, S), w1) = (w', s')

       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)
let rec transformInit(psi,  , l,  , (a,  , s),  , w1) let let  inlet  in(* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
let rec transformInit'((nil,  , mnil),  , uni type,  , (w,  , s)) (w,  , s) transformInit'((app (u,  , s),  , mapp (marg (minus,  , _),  , mS)),  , pi (_,  , v2),  , (w,  , s)) let let  inlet  in in transformInit' ((s,  , mS),  , v2,  , (w',  , s')) transformInit'((app (u,  , s),  , mapp (marg (plus,  , _),  , mS)),  , pi ((dec (name,  , v1),  , _),  , v2),  , (w,  , s)) let let  inlet  inlet  inlet  in in transformInit' ((s,  , mS),  , v2,  , (w',  , s')) in transformInit' ((s,  , mS),  , v,  , (id,  , createIHSub (psi,  , l)))(* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
let rec transformConc((a,  , s),  , w) let let rec transformConc'(nil,  , mnil) unit transformConc'(app (u,  , s'),  , mapp (marg (plus,  , _),  , mS')) transformConc' (s',  , mS') transformConc'(app (u,  , s'),  , mapp (marg (minus,  , _),  , mS')) pairExp (strengthenExp (u,  , w),  , transformConc' (s',  , mS')) in transformConc' (s,  , modeSpine a)(* renameExp f U = U'

       Invariant:
       U' = U module application of f to any projectoin contained
       in U.
    *)
let rec renameExpf(u as uni _) u renameExpf(pi ((d,  , dP),  , v)) pi ((renameDec f d,  , dP),  , renameExp f v) renameExpf(root (h,  , s)) root (renameHead f h,  , renameSpine f s) renameExpf(lam (d,  , u)) lam (renameDec f d,  , renameExp f u) renameDecf(dec (x,  , v)) dec (x,  , renameExp f v) renameHeadf(proj bi) f bi renameHeadfh h renameSpinefnil nil renameSpinef(app (u,  , s)) app (renameExp f u,  , renameSpine f s)let rec rename(bDec (_,  , (c,  , s)),  , v) let let  inlet rec makeSubst(n,  , g,  , s,  , nil,  , f) (g,  , f) makeSubst(n,  , g,  , s,  , (d as dec (x,  , v')) :: l,  , f) if belowEq (targetFam v',  , targetFam v) then makeSubst (n + 1,  , decl (g,  , decSub (d,  , s)),  , dot1 s,  , l,  , f) else makeSubst (n,  , g,  , comp (s,  , shift),  , l,  , f)let  in in (g,  , renameExp f v)let rec append(g,  , null) g append(g,  , decl (g',  , d)) decl (append (g,  , g'),  , d)(* traverseNeg (L, wmap, projs)  (Psi0, Psi, V) = ([w', PQ'], L')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- V : type
           then L' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)
let rec traverseNeg(l,  , wmap,  , projs)((psi0,  , psi),  , pi ((d as dec (_,  , v1),  , maybe),  , v2),  , w) (match traverseNeg (l,  , wmap,  , projs) ((psi0,  , decl (psi,  , uDec d)),  , v2,  , dot1 w) with (sOME (w',  , pQ')) -> sOME (peel w',  , pQ')) traverseNeg(l,  , wmap,  , projs)((psi0,  , psi),  , pi ((d as dec (_,  , v1),  , no),  , v2),  , w) (match traverseNeg (l,  , wmap,  , projs) ((psi0,  , decl (psi,  , uDec d)),  , v2,  , comp (w,  , shift)) with (sOME (w',  , pQ')) -> traversePos (l,  , wmap,  , projs) ((psi0,  , psi,  , null),  , v1,  , sOME (peel w',  , pQ'))) traverseNeg(l,  , wmap,  , projs)((psi0,  , psi),  , root (const a,  , s),  , w) let let  in(* Psi1 = Psi0, Psi *)
let  in(* Psi1 |- w0 : Psi0 *)
let  in(* |- Psi' ctx *)
(* Psi1 |- w' : Psi' *)
let  in(* Psi' |- s'' : G+ *)
(* G |- w'' : G+ *)
let  in in (sOME (w',  , (fun p -> (psi',  , s'',  , p),  , transformConc ((a,  , s),  , w)))) traversePos(l,  , wmap,  , projs)((psi0,  , psi,  , g),  , pi ((d as bDec (x,  , (c,  , s)),  , _),  , v),  , sOME (w1,  , (p,  , q))) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in traversePos (l,  , wmap,  , projs) ((psi0,  , psi,  , decl (g,  , (* T.UDec *)
, (bDec (x,  , (c',  , s))))),  , v,  , sOME (dot1 w1,  , (p,  , q))) traversePos(l,  , wmap,  , projs)((psi0,  , g,  , b),  , v as root (const a,  , s),  , sOME (w1,  , (p,  , q))) let let  in(* Psi1 = Psi0, G, B *)
let  inlet  in(* n = |Psi0, G', B'| *)
let  in(* m = |Psi0| *)
let rec lookupbasea let let  inlet  inlet  in in (const l,  , f)let rec lookup(([b],  , nONE,  , f),  , a) if a = b then let let  in in (p,  , f) else lookupbase a lookup(([b],  , sOME [lemma],  , f),  , a) if a = b then let let  in in (p,  , f) else lookupbase a lookup((b :: l,  , sOME (lemma :: lemmas),  , and (f1,  , f2)),  , a) if a = b then let let  in in (p,  , f1) else lookup ((l,  , sOME lemmas,  , f2),  , a)(* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
let  in(* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
let rec apply((s,  , mS),  , ft) applyW ((s,  , mS),  , whnfFor (ft)) applyW((nil,  , mnil),  , ft') (nil,  , forSub ft') applyW((app (u,  , s),  , mapp (marg (plus,  , _),  , mS)),  , (all (d,  , f'),  , t')) let let  in(* Psi0, G', B' |- U' : V' *)
let  in(* Psi0, G', B' |- F'' :: for *)
(* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
 in (appExp (u',  , s''),  , f'')(* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *)
 applyW((app (u,  , s),  , mapp (marg (minus,  , _),  , mS)),  , ft) applyW ((s,  , mS),  , ft)let  in(* Psi0, G', B' |- F'' :: for *)
(* Psi0, G', B' |- S'' :: F' >> F'' *)
let  inlet  in(* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
(* Psi0, G', B' |- P'' :: F'' *)
let  in(* b = |B| = |B'| *)
let  in(* Psi0, G |- w1' : Psi0, G' *)
let  in(* |- Psi0, G', B' ctx *)
let  in(* n' = |Psi0, G'| *)
let rec subCtx(null,  , s) (null,  , s) subCtx(decl (g,  , d),  , s) let let  in in (decl (g',  , decSub (d,  , s')),  , dot1 s')let  inlet  inlet  in(* Psi0, G' |- GB' ctx *)
let  inlet  in(* Psi0, G, B |- w1 : Psi0, G', B' *)
(* Psi0, G', GB'  |- s' : Psi0, G', B' *)
(* Psi0, G', GB' |- RR for *)
let  in(* Psi0, G |- w1' : Psi0, G' *)
(* Psi0, G' |- F''' for *)
(* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
let rec lift(null,  , p) p lift(decl (g,  , d),  , p) let let  in in lift (g,  , new (lam (uDec d,  , p)))let  in(* Psi0, G' |- P''' :: F''' *)
let  inlet  inlet  in(* |- Psi0, Psi1'' ctx *)
(* Psi0, G, B |- w2 : Psi1'' *)
(* Psi1'' = Psi0, G3, B3' *)
(* |B| = |GB'| *)
(* Psi'' |-  z2 : Psi0, G', B' *)
(* Psi0, G, B |- w2 : Psi0, G3, B3' *)
let  in(* Psi0, G |- w3 : Psi0, G3 *)
let  in(* Psi0, G3 |-  z3 : Psi0, G' *)
let  in(* Psi2 = Psi0, G3 *)
let  in(* Psi0, G3, B3' |- Pat' :: For *)
let  in(* Psi0, G3 |- F4 for *)
let  inlet  inlet  in(* ' F4 *)
let  inlet  inlet  in(* Psi0, G3 |- Pat :: F4  *)
(* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
let  inlet  in(* Psi0, G3 |- t :: Psi0, G', x :: F4  *)
 in (sOME (w3,  , (fun p -> p (let (pDec (nONE,  , f''',  , nONE,  , nONE),  , p''',  , case (cases [(psi2,  , t,  , p)]))),  , q)))(* traverse (Psi0, L, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  L is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (G, V) in Sig the following holds:
                    Psi0, G |- V : type
               and  head (V) in L
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (G, V) in Sig)
    *)
let rec traverse(psi0,  , l,  , sig,  , wmap,  , projs) let let rec traverseSig'nil nil traverseSig'((g,  , v) :: sig) (typeCheck (append (coerceCtx psi0,  , g),  , (v,  , uni type)); match traverseNeg (l,  , wmap,  , projs) ((psi0,  , embedCtx g),  , v,  , id) with (sOME (wf,  , (p',  , q'))) -> traverseSig' sig @ [(p' q')]) in traverseSig' sig(* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
    *)
let rec transformWorlds(fams,  , worlds cids) let (* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *)
let rec transformList(nil,  , w) nil transformList((d as dec (x,  , v)) :: l,  , w) if foldr (fun (a,  , b) -> b && belowEq (a,  , targetFam v)) true fams then transformList (l,  , comp (w,  , shift)) else let let  in in (dec (x,  , strengthenExp (v,  , w))) :: l'let rec transformWorlds'(nil) (nil,  , fun c -> raise (error "World not found")) transformWorlds'(cid :: cids') let let  in(* Design decision: Let's keep all of G *)
let  inlet  inlet  in in (cid' :: cids'',  , fun c -> if c = cid then cid' else wmap c)let  in in (worlds cids',  , wmap)(* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)
let rec dynamicSig(psi0,  , a,  , worlds cids) let (* findDec (G, n, L, s, S) = S'

             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
let rec findDec(g,  , _,  , nil,  , w,  , sig) sig findDec(g,  , n,  , d :: l,  , w,  , sig) let let  inlet  inlet  in in findDec (g,  , n + 1,  , l,  , dot (exp (root (proj (bidx 1,  , n),  , nil)),  , w),  , sig')(* mediateSub G = (G0, s)

             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *)
let rec mediateSub(null) (null,  , shift (ctxLength psi0)) mediateSub(decl (g,  , d)) let let  inlet  in in (decl (g0,  , d'),  , dot1 s')let rec findDecs'(nil,  , sig) sig findDecs'(cid :: cids',  , sig) let let  in(* G |- L ctx *)
let  in(* Psi0, G0 |- s'' : G *)
let  in(* Psi0, G0 |- D : dec *)
let  in(* Psi0, G0, D' |- s'' : G *)
let  in in findDecs' (cids',  , sig') in findDecs' (cids,  , nil)(* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)
let rec staticSig(psi0,  , nil) nil staticSig(psi0,  , conDec (name,  , _,  , _,  , _,  , v,  , type) :: sig) (null,  , normalize (v,  , shift (ctxLength psi0))) :: staticSig (psi0,  , sig)let rec name[a] conDecName (sgnLookup a) name(a :: l) conDecName (sgnLookup a) ^ "/" ^ (name l)(* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in L into functional form
    *)
let rec convertPrg(l,  , projs) let let  inlet  inlet  inlet  inlet rec convertWorlds[a] let let  in(* W describes the world of a *)
 in w convertWorlds(a :: l') let let  in(* W describes the world of a *)
let  in in if eqWorlds (w,  , w') then w' else raise (error "Type families different in different worlds")let  inlet  inlet rec convertOnePrg(a,  , f) let let  inlet  in(* Psi0 |- {x1:V1} ... {xn:Vn} type *)
let  in(* |- mS : {x1:V1} ... {xn:Vn} > type *)
let  in(* Sig in LF(reg)   *)
let  inlet  inlet  inlet  inlet  inlet  in(* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
let rec init(all ((d,  , _),  , f')) let let  in in (f'',  , fun p -> lam (d,  , p' p)) initf' (f',  , fun p -> p)let  inlet  in(* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
 in pinit (case ((* F', *)
cases (c0 @ c)))let rec convertPrg'(nil,  , _) raise (error "Cannot convert Empty program") convertPrg'([a],  , f) convertOnePrg (a,  , f) convertPrg'(a :: l',  , and (f1,  , f2)) pairPrg (convertOnePrg (a,  , f1),  , convertPrg' (l',  , f2))let  in in plet rec installFor[cid] let let  inlet  inlet  in in ()let rec depthConj(and (f1,  , f2)) 1 + depthConj f2 depthConjf 1let rec createProjection(psi,  , depth,  , f as and (f1,  , f2),  , pattern) createProjection (decl (psi,  , pDec (nONE,  , f1,  , nONE,  , nONE)),  , depth + 1,  , forSub (f2,  , shift 1),  , pairPrg (var (depth + 2),  , pattern)) createProjection(psi,  , depth,  , f,  , pattern) let let  inlet  in in fun k -> let let  in in (case (cases [(psi',  , dot (prg (pattern),  , shift (depth')),  , var k)]),  , f')let rec installProjection(nil,  , _,  , f,  , proj) nil installProjection(cid :: cids,  , n,  , f,  , proj) let let  inlet  inlet  inlet  inlet  inlet  in in lemma :: installProjection (cids,  , n - 1,  , f,  , proj)let rec installSelection([cid],  , [lemma],  , f1,  , main) let let  inlet  inlet  inlet  in in [lemma'] installSelection(cid :: cids,  , lemma :: lemmas,  , and (f1,  , f2),  , main) let let  inlet  inlet  inlet  in in lemma' :: installSelection (cids,  , lemmas,  , f2,  , main)let rec installPrg[cid] let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (lemma,  , [],  , []) installPrgcids let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (lemma,  , projs,  , sels)let rec mkResult0 unit mkResultn pairExp (root (bVar n,  , nil),  , mkResult (n - 1))let rec convertGoal(g,  , v) let let  inlet  inlet  inlet  inlet  in in p''let  inlet  inlet  inlet  inlet  inlet  inend