MTPAbstract  StateSyn' STATESYN    Whnf WHNF    Constraints CONSTRAINTS    Unify UNIFY    Subordinate SUBORDINATE    TypeCheck TYPECHECK    FunTypeCheck FUNTYPECHECK    FunTypeCheck StateSyn  StateSyn'   Abstract ABSTRACT     MTPABSTRACT  struct (*! structure IntSyn = IntSyn' !*)
(*! structure FunSyn = FunSyn' !*)
module exception type ApproxFor(*      | (t, G2), AF *)
module module module module (* Intermediate Data Structure *)
type EBVar(*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
(* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
let rec checkEmpty(nil) () checkEmpty(cnstrL) (match simplify cnstrL with nil -> () _ -> raise (error "Typing ambiguous -- unresolved constraints"))(* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
let rec eqEVar(eVar (r1,  , _,  , _,  , _))(eV (r2,  , _,  , _,  , _)) (r1 = r2) eqEVar__ false(* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
let rec existspk let let rec exists'(null) false exists'(decl (k',  , y)) p (y) || exists' (k') in exists' klet rec or(maybe,  , _) maybe or(_,  , maybe) maybe or(meta,  , _) meta or(_,  , meta) meta or(no,  , no) no(* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
let rec occursInExp(k,  , uni _) no occursInExp(k,  , pi (dP,  , v)) or (occursInDecP (k,  , dP),  , occursInExp (k + 1,  , v)) occursInExp(k,  , root (h,  , s)) occursInHead (k,  , h,  , occursInSpine (k,  , s)) occursInExp(k,  , lam (d,  , v)) or (occursInDec (k,  , d),  , occursInExp (k + 1,  , v))(* no case for Redex, EVar, EClo *)
 occursInHead(k,  , bVar (k'),  , dP) if (k = k') then maybe else dP occursInHead(k,  , const _,  , dP) dP occursInHead(k,  , def _,  , dP) dP occursInHead(k,  , skonst _,  , no) no occursInHead(k,  , skonst _,  , meta) meta occursInHead(k,  , skonst _,  , maybe) meta(* no case for FVar *)
 occursInSpine(_,  , nil) no occursInSpine(k,  , app (u,  , s)) or (occursInExp (k,  , u),  , occursInSpine (k,  , s))(* no case for SClo *)
 occursInDec(k,  , dec (_,  , v)) occursInExp (k,  , v) occursInDecP(k,  , (d,  , _)) occursInDec (k,  , d)(* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
(* optimize to have fewer traversals? -cs *)
(* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
let rec piDepend(dPV as ((d,  , no),  , v)) pi dPV piDepend(dPV as ((d,  , meta),  , v)) pi dPV piDepend((d,  , maybe),  , v) pi ((d,  , occursInExp (1,  , v)),  , v)(* weaken (depth,  G, a) = (w')
    *)
let rec weaken(null,  , a) id weaken(decl (g',  , d as dec (name,  , v)),  , a) let let  in in if belowEq (targetFam v,  , a) then dot1 w' else comp (w',  , shift)(* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , pi ((d,  , maybe),  , v))let rec restore(0,  , gp) (gp,  , null) restore(n,  , decl (g,  , d)) let let  in in (gp',  , decl (gX',  , d))let rec concat(gp,  , null) gp concat(gp,  , decl (g,  , d)) decl (concat (gp,  , g),  , d)(* collectExpW (T, d, G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)
(* Possible optimization: Calculate also the normal form of the term *)
let rec collectExpW(t,  , d,  , g,  , (uni l,  , s),  , k) k collectExpW(t,  , d,  , g,  , (pi ((d,  , _),  , v),  , s),  , k) collectExp (t,  , d,  , decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , collectDec (t,  , d,  , g,  , (d,  , s),  , k)) collectExpW(t,  , d,  , g,  , (root (_,  , s),  , s),  , k) collectSpine (decrease t,  , d,  , g,  , (s,  , s),  , k) collectExpW(t,  , d,  , g,  , (lam (d,  , u),  , s),  , k) collectExp (t,  , d,  , decl (g,  , decSub (d,  , s)),  , (u,  , dot1 s),  , collectDec (t,  , d,  , g,  , (d,  , s),  , k)) collectExpW(t,  , d,  , g,  , (x as eVar (r,  , gdX,  , v,  , cnstrs),  , s),  , k) if exists (eqEVar x) k then collectSub (t,  , d,  , g,  , s,  , k) else let let  in(* optimization possible for d = 0 *)
let  inlet  inlet  inlet  inlet  inlet  inlet  in in collectSub (t,  , d,  , g,  , comp (w,  , s),  , decl (collectExp (t,  , d,  , gp,  , (v',  , id),  , k),  , eV (r',  , v',  , t,  , d))) collectExpW(t,  , d,  , g,  , (fgnExp csfe,  , s),  , k) fold csfe (fun (u,  , k') -> collectExp (t,  , d,  , g,  , (u,  , s),  , k')) k(* hack - should consult cs    -rv *)
(* No other cases can occur due to whnf invariant *)
(* collectExp (T, d, G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
 collectExp(t,  , d,  , g,  , us,  , k) collectExpW (t,  , d,  , g,  , whnf us,  , k)(* collectSpine (T, d, G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
 collectSpine(t,  , d,  , g,  , (nil,  , _),  , k) k collectSpine(t,  , d,  , g,  , (sClo (s,  , s'),  , s),  , k) collectSpine (t,  , d,  , g,  , (s,  , comp (s',  , s)),  , k) collectSpine(t,  , d,  , g,  , (app (u,  , s),  , s),  , k) collectSpine (t,  , d,  , g,  , (s,  , s),  , collectExp (t,  , d,  , g,  , (u,  , s),  , k))(* collectDec (T, d, G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
 collectDec(t,  , d,  , g,  , (dec (_,  , v),  , s),  , k) collectExp (t,  , d,  , g,  , (v,  , s),  , k)(* collectSub (T, d, G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
 collectSub(t,  , d,  , g,  , shift _,  , k) k collectSub(t,  , d,  , g,  , dot (idx _,  , s),  , k) collectSub (t,  , d,  , g,  , s,  , k) collectSub(t,  , d,  , g,  , dot (exp (u),  , s),  , k) collectSub (t,  , d,  , g,  , s,  , collectExp (t,  , d,  , g,  , (u,  , id),  , k))(* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
let rec abstractEVar(decl (k',  , eV (r',  , _,  , _,  , d)),  , depth,  , x as eVar (r,  , _,  , _,  , _)) if r = r' then (bVar (depth + 1),  , d) else abstractEVar (k',  , depth + 1,  , x) abstractEVar(decl (k',  , bV _),  , depth,  , x) abstractEVar (k',  , depth + 1,  , x)(* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
let rec lookupBV(k,  , i) let let rec lookupBV'(decl (k,  , eV (r,  , v,  , _,  , _)),  , i,  , k) lookupBV' (k,  , i,  , k + 1) lookupBV'(decl (k,  , bV _),  , 1,  , k) k lookupBV'(decl (k,  , bV _),  , i,  , k) lookupBV' (k,  , i - 1,  , k + 1)(* lookupBV' I.Null cannot occur by invariant *)
 in lookupBV' (k,  , i,  , 1)(* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
let rec abstractExpW(k,  , depth,  , (u as uni (l),  , s)) u abstractExpW(k,  , depth,  , (pi ((d,  , p),  , v),  , s)) piDepend ((abstractDec (k,  , depth,  , (d,  , s)),  , p),  , abstractExp (k,  , depth + 1,  , (v,  , dot1 s))) abstractExpW(k,  , depth,  , (root (h as bVar k,  , s),  , s)) if k > depth then let let  in in root (bVar (k' + depth),  , abstractSpine (k,  , depth,  , (s,  , s))) else root (h,  , abstractSpine (k,  , depth,  , (s,  , s))) abstractExpW(k,  , depth,  , (root (h,  , s),  , s)) root (h,  , abstractSpine (k,  , depth,  , (s,  , s))) abstractExpW(k,  , depth,  , (lam (d,  , u),  , s)) lam (abstractDec (k,  , depth,  , (d,  , s)),  , abstractExp (k,  , depth + 1,  , (u,  , dot1 s))) abstractExpW(k,  , depth,  , (x as eVar (_,  , g,  , _,  , _),  , s)) let let  in in root (h,  , abstractSub (ctxLength g - d,  , k,  , depth,  , s,  , nil)) abstractExpW(k,  , depth,  , (fgnExp csfe,  , s)) apply csfe (fun u -> abstractExp (k,  , depth,  , (u,  , s)))(* hack - should consult cs   -rv *)
(* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
 abstractExp(k,  , depth,  , us) abstractExpW (k,  , depth,  , whnf us)(* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
 abstractSub(n,  , k,  , depth,  , shift (k),  , s) if n > 0 then abstractSub (n,  , k,  , depth,  , dot (idx (k + 1),  , shift (k + 1)),  , s) else (* n = 0 *)
s abstractSub(n,  , k,  , depth,  , dot (idx (k),  , s),  , s) let let  in in abstractSub (n - 1,  , k,  , depth,  , s,  , app (root (h,  , nil),  , s)) abstractSub(n,  , k,  , depth,  , dot (exp (u),  , s),  , s) abstractSub (n - 1,  , k,  , depth,  , s,  , app (abstractExp (k,  , depth,  , (u,  , id)),  , s))(* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
 abstractSpine(k,  , depth,  , (nil,  , _)) nil abstractSpine(k,  , depth,  , (sClo (s,  , s'),  , s)) abstractSpine (k,  , depth,  , (s,  , comp (s',  , s))) abstractSpine(k,  , depth,  , (app (u,  , s),  , s)) app (abstractExp (k,  , depth,  , (u,  , s)),  , abstractSpine (k,  , depth,  , (s,  , s)))(* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
 abstractDec(k,  , depth,  , (dec (x,  , v),  , s)) dec (x,  , abstractExp (k,  , depth,  , (v,  , s)))(* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
let rec getLevel(uni _) kind getLevel(pi (_,  , u)) getLevel u getLevel(root _) type getLevel(redex (u,  , _)) getLevel u getLevel(lam (_,  , u)) getLevel u getLevel(eClo (u,  , _)) getLevel u(* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
let rec checkTypev (match getLevel v with type -> () _ -> raise (error "Typing ambiguous -- free type variable"))(* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
let rec abstractCtx(null) (null,  , null) abstractCtx(decl (k',  , eV (_,  , v',  , t as lemma (b),  , _))) let let  inlet  inlet  inlet  in in (decl (g',  , d'),  , decl (b',  , t)) abstractCtx(decl (k',  , eV (_,  , v',  , t as none,  , _))) let let  inlet  inlet  inlet  in in (decl (g',  , d'),  , decl (b',  , none)) abstractCtx(decl (k',  , bV (d,  , t))) let let  inlet  in in (decl (g',  , d'),  , decl (b',  , t))(* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)
let rec abstractGlobalSub(k,  , shift _,  , null) shift (ctxLength k) abstractGlobalSub(k,  , shift n,  , b as decl _) abstractGlobalSub (k,  , dot (idx (n + 1),  , shift (n + 1)),  , b) abstractGlobalSub(k,  , dot (idx k,  , s'),  , decl (b,  , t as parameter _)) dot (idx (lookupBV (k,  , k)),  , abstractGlobalSub (k,  , s',  , b)) abstractGlobalSub(k,  , dot (exp u,  , s'),  , decl (b,  , t as lemma _)) dot (exp (abstractExp (k,  , 0,  , (u,  , id))),  , abstractGlobalSub (k,  , s',  , b))(* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
let rec collectGlobalSub(g0,  , shift _,  , null,  , collect) collect collectGlobalSub(g0,  , s,  , b as decl (_,  , parameter (sOME l)),  , collect) let let  in in skip (g0,  , length g2,  , s,  , b,  , collect) collectGlobalSub(g0,  , dot (exp (u),  , s),  , decl (b,  , t),  , collect) collectGlobalSub (g0,  , s,  , b,  , fun (d,  , k) -> collect (d,  , collectExp (t,  , d,  , g0,  , (u,  , id),  , k)))(* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)
 skip(g0,  , 0,  , s,  , b,  , collect) collectGlobalSub (g0,  , s,  , b,  , collect) skip(decl (g0,  , d),  , n,  , s,  , decl (b,  , t as parameter _),  , collect) skip (g0,  , n - 1,  , invDot1 s,  , b,  , fun (d,  , k) -> collect (d + 1,  , decl (k,  , bV (d,  , t))))(* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
let rec abstractNew((g0,  , b0),  , s,  , b) let let  inlet  in in (abstractCtx k,  , abstractGlobalSub (k,  , s,  , b))(* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
let rec abstractSubAll(t,  , b1,  , (g0,  , b0),  , s,  , b) let (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
let rec skip''(k,  , (null,  , null)) k skip''(k,  , (decl (g0,  , d),  , decl (b0,  , t))) decl (skip'' (k,  , (g0,  , b0)),  , bV (d,  , t))let  inlet  inlet  inlet  inlet  inlet  in in (abstractCtx k,  , abstractGlobalSub (k,  , s,  , b))(* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
let rec abstractFor(k,  , depth,  , (all (prim d,  , f),  , s)) all (prim (abstractDec (k,  , depth,  , (d,  , s))),  , abstractFor (k,  , depth + 1,  , (f,  , dot1 s))) abstractFor(k,  , depth,  , (ex (d,  , f),  , s)) ex (abstractDec (k,  , depth,  , (d,  , s)),  , abstractFor (k,  , depth + 1,  , (f,  , dot1 s))) abstractFor(k,  , depth,  , (true,  , s)) true abstractFor(k,  , depth,  , (and (f1,  , f2),  , s)) and (abstractFor (k,  , depth,  , (f1,  , s)),  , abstractFor (k,  , depth,  , (f2,  , s)))(* abstract (Gx, F) = F'

       Invariant:
       If   G, Gx |- F formula
       then G |- F' = {{Gx}} F formula
    *)
let rec allClo(null,  , f) f allClo(decl (gx,  , d),  , f) allClo (gx,  , all (prim d,  , f))let rec convert(null) null convert(decl (g,  , d)) decl (convert g,  , bV (d,  , parameter nONE))let rec createEmptyB0 null createEmptyB(n) decl (createEmptyB (n - 1),  , none)let rec lower(_,  , 0) null lower(decl (g,  , d),  , n) decl (lower (g,  , n - 1),  , d)let rec split(g,  , 0) (g,  , null) split(decl (g,  , d),  , n) let let  in in (g1,  , decl (g2,  , d))(* shift G = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, G ctx
       then G0, V, G |- s' : G0, G
    *)
let rec shift(null) shift shift(decl (g,  , _)) dot1 (shift g)(* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
let rec ctxSub(nil,  , s) nil ctxSub(d :: g,  , s) decSub (d,  , s) :: ctxSub (g,  , dot1 s)(* weaken2 (G, a, i, S) = w'

       Invariant:
       G |- w' : Gw
       Gw < G
       G |- S : {Gw} V > V
    *)
let rec weaken2(null,  , a,  , i) (id,  , fun s -> s) weaken2(decl (g',  , d as dec (name,  , v)),  , a,  , i) let let  in in if belowEq (targetFam v,  , a) then (dot1 w',  , fun s -> app (root (bVar i,  , nil),  , s)) else (comp (w',  , shift),  , s')(* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , piDepend ((normalizeDec (d,  , id),  , maybe),  , v))(* raiseFor (G, F, w, sc) = F'

       Invariant:
       If   G0 |- G ctx
       and  G0, G, GF |- F for
       and  G0, {G} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, G[..] |- s : G0, G, GF)
       then G0, {G} GF |- F' for
    *)
let rec raiseFor(k,  , gorig,  , f as true,  , w,  , sc) f raiseFor(k,  , gorig,  , ex (dec (name,  , v),  , f),  , w,  , sc) let let  inlet  inlet  in(* G0, {G}GF[..], G |- s : G0, G, GF *)
let  in(* G0, {G}GF[..], G |- V' : type *)
let  in(* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
let  in(* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
let  in(* Generalize the invariant for Whnf.strengthen --cs *)
let  in(* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
let  in(* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
let  in(* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
(* G0, {G}GF[..], G |- s : G0, G, GF *)
let  inlet  in in ex (dec (name,  , v'''),  , f') raiseFor(k,  , gorig,  , all (prim (dec (name,  , v)),  , f),  , w,  , sc) let (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)
                  val V' = Whnf.normalize (raiseType (G, Whnf.normalize (V, s)), I.id)
                                        (* G0, {G}GF[..] |- V' = {G}(V[s]) : type *)
                  val S' = spine g
                                        (* G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] *)
                  val sc' = fn (w', k') =>
                              let
                                        (* G0, GA |- w' : G0 *)
                                val s' = sc (w', k')
                                        (* G0, GA, G[..] |- s' : G0, G, GF *)
                              in
                                I.Dot (I.Exp (I.Root (I.BVar (g + k'-k), S')), s')
                                        (* G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V *)
                              end
                  val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
                in
                  F.All (F.Prim (I.Dec (name, V')), F')
*)
let  inlet  inlet  in(* G0, {G}GF[..], G |- s : G0, G, GF *)
let  in(* G0, {G}GF[..], G |- V' : type *)
let  in(* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
let  in(* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
let  in(* Generalize the invariant for Whnf.strengthen --cs *)
let  in(* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
let  in(* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
let  in(* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
(* G0, {G}GF[..], G |- s : G0, G, GF *)
let  inlet  in in all (prim (dec (name,  , v''')),  , f')(* the other case of F.All (F.Block _, _) is not yet covered *)
let rec extend(k,  , nil) k extend(k,  , d :: l) extend (decl (k,  , bV (d,  , none)),  , l)(* makeFor (G, w, AF) = F'

       Invariant :
       If   |- G ctx
       and  G |- w : G'
       and  G' |- AF approx for
       then G'; . |- F' = {EVARS} AF  for
    *)
let rec makeFor(k,  , w,  , head (g,  , (f,  , s),  , d)) let let  inlet  inlet  inlet  inlet  inlet  in(*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
let  inlet  inlet  inlet  in in (gK1,  , allClo (gK2,  , fK)) makeFor(k,  , w,  , block ((g,  , t,  , d,  , g2),  , aF)) let let  inlet  inlet  in(* BUG *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in (gK11,  , f''')let rec abstractApproxFor(aF as head (g,  , _,  , _)) let let  in in f abstractApproxFor(aF as block ((g,  , _,  , _,  , _),  , _)) let let  in in flet  inlet  inlet  inlet  inlet  inend