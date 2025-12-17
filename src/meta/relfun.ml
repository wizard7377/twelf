RelFun  Global GLOBAL    ModeTable MODETABLE    Names NAMES    Unify UNIFY    Whnf WHNF    Weaken WEAKEN    TypeCheck TYPECHECK    FunWeaken FUNWEAKEN    FunNames FUNNAMES     RELFUN  struct (*! structure FunSyn = FunSyn' !*)
exception module module module (* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
let rec ctxSub(null,  , s) (null,  , s) ctxSub(decl (g,  , d),  , s) let let  in in (decl (g',  , decSub (d,  , s')),  , dot1 s)let rec convertOneForcid let let  inlet  in(* convertFor' (V, mS, w1, w2, n) = (F', F'')

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
let rec convertFor'(pi ((d,  , _),  , v),  , mapp (marg (plus,  , _),  , mS),  , w1,  , w2,  , n) let let  in in (fun f -> all (prim (strengthenDec (d,  , w1)),  , f' f),  , f'') convertFor'(pi ((d,  , _),  , v),  , mapp (marg (minus,  , _),  , mS),  , w1,  , w2,  , n) let let  in in (f',  , ex (decSub (d,  , w2),  , f'')) convertFor'(uni type,  , mnil,  , _,  , _,  , _) (fun f -> f,  , true) convertFor'_ raise (error "type family must be +/- moded")(* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
let rec shiftPlusmS let let rec shiftPlus'(mnil,  , n) n shiftPlus'(mapp (marg (plus,  , _),  , mS'),  , n) shiftPlus' (mS',  , n + 1) shiftPlus'(mapp (marg (minus,  , _),  , mS'),  , n) shiftPlus' (mS',  , n) in shiftPlus' (mS,  , 0)let  inlet  in in f f'(* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
let rec convertFornil raise (error "Empty theorem") convertFor[a] convertOneFor a convertFor(a :: l) and (convertOneFor a,  , convertFor l)(* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
let rec occursInExpN(k,  , uni _) false occursInExpN(k,  , pi (dP,  , v)) occursInDecP (k,  , dP) || occursInExpN (k + 1,  , v) occursInExpN(k,  , root (h,  , s)) occursInHead (k,  , h) || occursInSpine (k,  , s) occursInExpN(k,  , lam (d,  , v)) occursInDec (k,  , d) || occursInExpN (k + 1,  , v) occursInExpN(k,  , fgnExp csfe) fold csfe (fun (u,  , b) -> b || occursInExpN (k,  , normalize (u,  , id))) false(* no case for Redex, EVar, EClo *)
 occursInHead(k,  , bVar (k')) (k = k') occursInHead(k,  , const _) false occursInHead(k,  , def _) false occursInHead(k,  , fgnConst _) false(* no case for FVar *)
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
let rec shiftinv(w) strengthenSub (w,  , shift)let rec eqIdx(idx (n),  , idx (k)) (n = k) eqIdx_ falselet rec peelw if eqIdx (bvarSub (1,  , w),  , idx 1) then dot1inv w else shiftinv wlet rec peeln(0,  , w) w peeln(n,  , w) peeln (n - 1,  , peel w)(* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
let rec domain(g,  , dot (idx _,  , s)) domain (g,  , s) + 1 domain(null,  , shift 0) 0 domain(g as decl _,  , shift 0) domain (g,  , dot (idx 1,  , shift 1)) domain(decl (g,  , _),  , shift n) domain (g,  , shift (n - 1))(* strenghten (Psi, (a, S), w, m) = (Psi', w')

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  |- Psi2 ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1
    *)
let rec strengthen(psi,  , (a,  , s),  , w,  , m) let let  inlet rec args(nil,  , mnil) nil args(app (u,  , s'),  , mapp (marg (m',  , _),  , mS)) let let  in in (match modeEqual (m,  , m') with true -> u :: l false -> l)let rec strengthenArgs(nil,  , s) nil strengthenArgs(u :: l,  , s) strengthenExp (u,  , s) :: strengthenArgs (l,  , s)let rec occursInArgs(n,  , nil) false occursInArgs(n,  , u :: l) (occursInExp (n,  , u) || occursInArgs (n,  , l))let rec occursInPsi(n,  , (nil,  , l)) occursInArgs (n,  , l) occursInPsi(n,  , (prim (dec (_,  , v)) :: psi1,  , l)) occursInExp (n,  , v) || occursInPsi (n + 1,  , (psi1,  , l)) occursInPsi(n,  , (block (ctxBlock (l,  , g)) :: psi1,  , l)) occursInG (n,  , g,  , fun n' -> occursInPsi (n',  , (psi1,  , l))) occursInG(n,  , null,  , k) k n occursInG(n,  , decl (g,  , dec (_,  , v)),  , k) occursInG (n,  , g,  , fun n' -> occursInExp (n',  , v) || k (n' + 1))let rec occursBlock(g,  , (psi2,  , l)) let let rec occursBlock(null,  , n) false occursBlock(decl (g,  , d),  , n) occursInPsi (n,  , (psi2,  , l)) || occursBlock (g,  , n + 1) in occursBlock (g,  , 1)(* testBlock (G, (bw, w1)) = (bw', w')

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
let rec inBlock(null,  , (bw,  , w1)) (bw,  , w1) inBlock(decl (g,  , d),  , (bw,  , w1)) if eqIdx (bvarSub (1,  , w1),  , idx 1) then inBlock (g,  , (true,  , dot1inv w1)) else inBlock (g,  , (bw,  , strengthenSub (w1,  , shift)))let rec blockSub(null,  , w) (null,  , w) blockSub(decl (g,  , dec (name,  , v)),  , w) let let  inlet  in in (decl (g',  , dec (name,  , v')),  , dot1 w')(* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

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
) (null,  , id) strengthen'(decl (psi1,  , lD as prim (dec (name,  , v))),  , psi2,  , l,  , w1) let let  in in if bw || occursInPsi (1,  , (psi2,  , l)) then let let  inlet  in in (decl (psi1',  , prim (dec (name,  , v'))),  , dot1 w') else let let  inlet  inlet  inlet  in in (psi1'',  , comp (w',  , shift)) strengthen'(decl (psi1,  , lD as block (ctxBlock (name,  , g))),  , psi2,  , l,  , w1) let let  in in if bw || occursBlock (g,  , (psi2,  , l)) then let let  inlet  in in (decl (psi1',  , block (ctxBlock (name,  , g''))),  , w'') else let let  inlet  inlet  in in strengthen' (psi1,  , psi2',  , l',  , w1') in strengthen' (psi,  , nil,  , args (s,  , mS),  , w)let rec recursionl let let  inlet rec name[a] conDecName (sgnLookup a) name(a :: l) conDecName (sgnLookup a) ^ "/" ^ (name l) in fun p -> rec (mDec (sOME (name l),  , f),  , p)(* abstract a = P'

       Invariant:
       If   a is a type family
       and  Sigma (a) = {x1:A1}..{xn:An} type
       then for all P s.t.
            +x1:A1, .., +xn:An; . |- P in [[-x1:A1]] .. [[-xn:An]] true
            . ;. |- (P' P) in [[+x1:A1]] .. [[+xn:An]] [[-x1:A1]] .. [[-xn:An]] true
    *)
let rec abstract(a) let let  inlet  in(* abstract' ((V, mS), w) = P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then P' is a Lam abstraction
        *)
let rec abstract'((_,  , mnil),  , w) (fun p -> p) abstract'((pi ((d,  , _),  , v2),  , mapp (marg (plus,  , _),  , mS)),  , w) let let  inlet  in in fun p -> lam (prim d',  , p p) abstract'((pi (_,  , v2),  , mapp (marg (minus,  , _),  , mS)),  , w) abstract' ((v2,  , mS),  , comp (w,  , shift)) in abstract' ((v,  , mS),  , id)(* transformInit (Psi, (a, S), w1) = (w', s')

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
let rec transformInit(psi,  , (a,  , s),  , w1) let let  inlet  in(* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
let rec transformInit'((nil,  , mnil),  , uni type,  , (w,  , s)) (w,  , s) transformInit'((app (u,  , s),  , mapp (marg (minus,  , _),  , mS)),  , pi (_,  , v2),  , (w,  , s)) let let  inlet  in in transformInit' ((s,  , mS),  , v2,  , (w',  , s')) transformInit'((app (u,  , s),  , mapp (marg (plus,  , _),  , mS)),  , pi ((dec (name,  , v1),  , _),  , v2),  , (w,  , s)) let let  inlet  inlet  inlet  in in transformInit' ((s,  , mS),  , v2,  , (w',  , s')) in transformInit' ((s,  , mS),  , v,  , (id,  , shift (lfctxLength psi)))(* transformDec (c'', (Psi+-, G0), d, (a, S), w1, w2, t) = (d', w', s', t', Ds)

       Invariant:
       If   |- Psi ctx
       and  Psi |- G0 ctx
       and  d = |Delta|
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi, G0 |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
       and  Psi |- w2 : Psi+-
       and  Psi+- |- t0 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi |- s' : Gamma+
       and  x1:A1 .. xn:An |- w': Gamma+    (w weakening substitution)
       and  Psi+- |- t' : Psi+, -x(k1):{G0} A(k1), ... -x(km):{G0} A(km)
       and  d' = |Delta'|
    *)
let rec transformDec(ts,  , (psi,  , g0),  , d,  , (a,  , s),  , w1,  , w2,  , t0) let let  inlet  in(* raiseExp (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
        *)
let rec raiseExp(g,  , u,  , a) let (* raiseExp G = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- G ctx
               and  Psi |- G' ctx   which ARE subordinate to a
               then Psi, G |- w : Psi, G'
               and  k is a continuation calculuting the right exprssion:
                    for all U, s.t. Psi, G |- U : V
                    Psi |- [[G']] U : {{G'}} V
            *)
let rec raiseExp'null (id,  , fun x -> x) raiseExp'(decl (g,  , d as dec (_,  , v))) let let  in in if belowEq (targetFam v,  , a) then (dot1 w,  , fun x -> k (lam (strengthenDec (d,  , w),  , x))) else (comp (w,  , shift),  , k)let  in in k (strengthenExp (u,  , w))(* raiseType (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
           and  Psi, G, x:{{G}} V |- x G : V
        *)
let rec raiseType(g,  , u,  , a) let (* raiseType (G, n) = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- G, Gv ctx
              and  Psi |- G' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, G |- w : Psi, G'
              and  k is a continuation calculating the right exprssion:
                   for all U, s.t. Psi, G |- U : V
                   Psi |- [[G']] U : {{G'}} V
              and  k' is a continuation calculating the corresponding spine:
                   for all S, s.t. Psi, G, G0,|- ... refine
            *)
let rec raiseType'(null,  , n) (id,  , fun x -> x,  , fun s -> s) raiseType'(decl (g,  , d as dec (_,  , v)),  , n) let let  in in if belowEq (targetFam v,  , a) then (dot1 w,  , fun x -> k (pi ((strengthenDec (d,  , w),  , maybe),  , x)),  , fun s -> app (root (bVar n,  , nil),  , s)) else (comp (w,  , shift),  , k,  , k')let  in in (k (strengthenExp (u,  , w)),  , root (bVar 1,  , k' nil))(* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some G, some V:
           Psi, V, G0 |- s' : Psi, G0, V
        *)
let rec exchangeSub(g0) let let  inlet rec exchangeSub'(0,  , s) s exchangeSub'(k,  , s) exchangeSub' (k - 1,  , dot (idx (k),  , s)) in dot (idx (g0 + 1),  , exchangeSub' (g0,  , shift (g0 + 1)))(* transformDec' (d, (S, mS), V, (z1, z2), (w, t)) = (d', w', t', (Ds+, Ds-))

           Invariant:
           If   Psi, G0 |- S : V > type
           and  S doesn't contain Skolem constants
           and  d = |Delta|
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
           and  Psi |- w2 : Psi+-
           and  Psi+- |- t : Psi+, -x1:{{G0}} A1... -xj:{{G0}} Aj
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1) |- z1: Psi+
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1), G0 |- z2: x1:A1...x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+- |- s' : +x1:A1 .. +xn:An
           and  Psi+- |- t' : Psi+, -x1:{{G0}} A1... -xn:{{G0}} An
           and  d' = |Delta'|
        *)
let rec transformDec'(d,  , (nil,  , mnil),  , uni type,  , (z1,  , z2),  , (w,  , t)) (w,  , t,  , (d,  , fun (k,  , ds) -> ds k,  , fun _ -> empty)) transformDec'(d,  , (app (u,  , s),  , mapp (marg (minus,  , _),  , mS)),  , pi ((dec (_,  , v1),  , dP),  , v2),  , (z1,  , z2),  , (w,  , t)) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (w'',  , t'',  , (d',  , dplus,  , fun k -> split (k,  , dminus 1))) transformDec'(d,  , (app (u,  , s),  , mapp (marg (plus,  , _),  , mS)),  , pi ((dec (name,  , v1),  , _),  , v2),  , (z1,  , z2),  , (w,  , t)) let let  inlet  inlet  inlet  inlet  inlet  inlet  in in (w'',  , t'',  , (d',  , fun (k,  , ds) -> app ((k,  , u'),  , dplus (1,  , ds)),  , dminus))let  in(* head Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', P')

             Invariant:
             If   a not in Ts  then d'= d+1,  P' makes a lemma call
             If   Ts = [a]     then d'= d     P' used directly the ih.
             If   Ts = a1 .. ai ... and ai = a
             then d' = d+i   and P' select ih, and then decomposes is, using
                  (i-1) Rights and 1 Left
          *)
let rec varHeadts(w'',  , t'',  , (d',  , dplus,  , dminus)) let let rec head'([a'],  , d1,  , k1) (d1,  , k1) head'(a' :: ts',  , d1,  , k1) if a = a' then (d1 + 1,  , fun xx -> left (xx,  , (k1 1))) else let let  in in (d2,  , fun xx -> right (xx,  , (k2 1)))let  in in (d2,  , w'',  , t'',  , k2 d)let rec lemmaHead(w'',  , t'',  , (d',  , dplus,  , dminus)) let let  inlet  in in (d' + 1,  , w'',  , t'',  , lemma (l,  , dplus (1,  , dminus))) in if exists (fun x -> x = a) ts then varHead ts (w'',  , t'',  , (d',  , dplus,  , dminus)) else lemmaHead (w'',  , t'',  , (d',  , dplus,  , dminus))(* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
let rec transformConc((a,  , s),  , w) let let  inlet rec transformConc'(nil,  , mnil) unit transformConc'(app (u,  , s'),  , mapp (marg (plus,  , _),  , mS')) transformConc' (s',  , mS') transformConc'(app (u,  , s'),  , mapp (marg (minus,  , _),  , mS')) inx (strengthenExp (u,  , w),  , transformConc' (s',  , mS')) in transformConc' (s,  , mS)(* traverse (Ts, c) = L'

       Invariant:
       If   Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then L' is a list of cases
    *)
let rec traverse(ts,  , c) let (* traverseNeg (c'', Psi, (V, v), L) = ([w', d', PQ'], L')    [] means optional

           Invariant:
           If   Psi0 |- V : type
           and  Psi0 |- v : Psi
           and  V[v^-1] does not contain Skolem constants
           and  c'' is the name of the object constant currently considered
           and  L is a list of cases
           then L' list of cases and CL' extends CL
           and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
           and  d' is the length of Delta
           and  PQ'  is a pair, generating the proof term
        *)
let rec traverseNeg(c'',  , psi,  , (pi ((d as dec (_,  , v1),  , maybe),  , v2),  , v),  , l) (match traverseNeg (c'',  , decl (psi,  , prim (strengthenDec (d,  , v))),  , (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (D, v)))),
*)
, (v2,  , dot1 v),  , l) with (sOME (w',  , d',  , pQ'),  , l') -> (sOME (peel w',  , d',  , pQ'),  , l') (nONE,  , l') -> (nONE,  , l')) traverseNeg(c'',  , psi,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , v),  , l) (match traverseNeg (c'',  , psi,  , (v2,  , comp (v,  , shift)),  , l) with (sOME (w',  , d',  , pQ'),  , l') -> traversePos (c'',  , psi,  , null,  , (strengthenExp (v1,  , v),  , id),  , sOME (w',  , d',  , pQ'),  , l') (nONE,  , l') -> traversePos (c'',  , psi,  , null,  , (strengthenExp (v1,  , v),  , id),  , nONE,  , l')) traverseNeg(c'',  , psi,  , (v as root (const c',  , s),  , v),  , l) if c = c' then let (* Clause head found *)
let  inlet  inlet  in in (sOME (w',  , 1,  , (fun p -> (psi',  , s'',  , p),  , fun wf -> transformConc ((c',  , s'),  , wf))),  , l) else (nONE,  , l)(* traversePos (c, Psi, G, (V, v), [w', d', PQ'], L) =  ([w'', d'', PQ''], L'')

           Invariant:
           If   Psi, G |- V : type
           and  Psi, G |- v : Psi'       (s.t.  Psi' |- V[v^-1] : type exists)
           and V[v^-1] does not contain Skolem constants
           [ and Psi', G |- w' : Psi''
             and |Delta'| = d'    for a Delta'
             and PQ' can generate the proof term so far in Delta'; Psi''
           ]
           and  c is the name of the constant currently considered
           and  L is a list of cases
           then L'' list of cases and L'' extends L
           and  Psi |- w'' : Psi2
           and  |Delta''| = d''  for a Delta'
           and  PQ'' can genreate the proof term so far in Delta''; Psi2
        *)
 traversePos(c'',  , psi,  , g,  , (pi ((d as dec (_,  , v1),  , maybe),  , v2),  , v),  , sOME (w,  , d,  , pQ),  , l) (match traversePos (c'',  , psi,  , decl (g,  , strengthenDec (d,  , v)),  , (v2,  , dot1 v),  , sOME (dot1 w,  , d,  , pQ),  , l) with (sOME (w',  , d',  , pQ'),  , l') -> (sOME (w',  , d',  , pQ'),  , l')) traversePos(c'',  , psi,  , g,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , v),  , sOME (w,  , d,  , pQ),  , l) (match traversePos (c'',  , psi,  , g,  , (v2,  , comp (v,  , shift)),  , sOME (w,  , d,  , pQ),  , l) with (sOME (w',  , d',  , pQ'),  , l') -> (match traverseNeg (c'',  , decl (psi,  , block (ctxBlock (nONE,  , g))),  , (v1,  , v),  , l') with (sOME (w'',  , d'',  , (p'',  , q'')),  , l'') -> (sOME (w',  , d',  , pQ'),  , (p'' (q'' w'')) :: l'') (nONE,  , l'') -> (sOME (w',  , d',  , pQ'),  , l''))) traversePos(c'',  , psi,  , null,  , (v,  , v),  , sOME (w1,  , d,  , (p,  , q)),  , l) let (* Lemma calls (no context block) *)
let  inlet  inlet  in(* provide typeCheckCtx from typecheck *)
let  inlet  in in (sOME (w2,  , d4,  , (fun p -> p (let (ds,  , case (opts [(psi',  , t4,  , p)]))),  , q)),  , l) traversePos(c'',  , psi,  , g,  , (v,  , v),  , sOME (w1,  , d,  , (p,  , q)),  , l) let (* Lemma calls (under a context block) *)
let  inlet  inlet  in(* provide typeCheckCtx from typecheck *)
let  inlet  inlet  in(* change w1 to w1' and w2 to w2' below *)
let  inlet  inlet  in in (sOME (w2',  , d4,  , (fun p -> p (let (new (ctxBlock (nONE,  , g1),  , ds),  , case (opts [(psi',  , t4,  , p)]))),  , q)),  , l) traversePos(c'',  , psi,  , g,  , (pi ((d as dec (_,  , v1),  , maybe),  , v2),  , v),  , nONE,  , l) traversePos (c'',  , psi,  , decl (g,  , strengthenDec (d,  , v)),  , (v2,  , dot1 v),  , nONE,  , l) traversePos(c'',  , psi,  , g,  , (pi ((d as dec (_,  , v1),  , no),  , v2),  , v),  , nONE,  , l) (match traversePos (c'',  , psi,  , g,  , (v2,  , comp (v,  , shift)),  , nONE,  , l) with (nONE,  , l') -> (match traverseNeg (c'',  , decl (psi,  , block (ctxBlock (nONE,  , g))),  , (v1,  , v),  , l') with (sOME (w'',  , d'',  , (p'',  , q'')),  , l'') -> (nONE,  , (p'' (q'' w'')) :: l'') (nONE,  , l'') -> (nONE,  , l''))) traversePos(c'',  , psi,  , g,  , (v,  , v),  , nONE,  , l) (nONE,  , l)let rec traverseSig'(c'',  , l) if c'' =  1 (sgnSize ()) then l else (match sgnLookup (c'') with conDec (name,  , _,  , _,  , _,  , v,  , type) -> (match traverseNeg (c'',  , null,  , (v,  , id),  , l) with (sOME (wf,  , d',  , (p',  , q')),  , l') -> traverseSig' (c'' + 1,  , (p' (q' wf)) :: l') (nONE,  , l') -> traverseSig' (c'' + 1,  , l')) _ -> traverseSig' (c'' + 1,  , l)) in traverseSig' (0,  , nil)(* convertPro Ts = P'

       Invariant:
       If   Ts is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in Ts into functional form
    *)
let rec convertProts let let rec convertOneProa let let  inlet  inlet  in in p (case (opts (traverse (ts,  , a))))let rec convertPro'nil raise (error "Cannot convert Empty program") convertPro'[a] convertOnePro a convertPro'(a :: ts') pair (convertOnePro a,  , convertPro' ts')let  in in r (convertPro' ts)let  inlet  inlet  inend