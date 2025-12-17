Abstract  Whnf WHNF    Unify UNIFY    Constraints CONSTRAINTS     ABSTRACT  struct exception module module module module (* Intermediate Data Structure *)
type EFLVar(*     | P                            *)
(*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)
(* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
let rec collectConstraints(null) nil collectConstraints(decl (g,  , fV _)) collectConstraints g collectConstraints(decl (g,  , eV (eVar (_,  , _,  , _,  , ref nil)))) collectConstraints g collectConstraints(decl (g,  , eV (eVar (_,  , _,  , _,  , ref cnstrL)))) (simplify cnstrL) @ collectConstraints g collectConstraints(decl (g,  , lV _)) collectConstraints g(* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)
let rec checkConstraints(k) let let  inlet  in in ()(* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
(*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error "Typing ambiguous -- unresolved constraints")
    *)
(* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
let rec eqEVar(eVar (r1,  , _,  , _,  , _))(eV (eVar (r2,  , _,  , _,  , _))) (r1 = r2) eqEVar__ false(* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
let rec eqFVar(fVar (n1,  , _,  , _))(fV (n2,  , _)) (n1 = n2) eqFVar__ false(* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
let rec eqLVar(lVar ((r1,  , _,  , _)))(lV (lVar ((r2,  , _,  , _)))) (r1 = r2) eqLVar__ false(* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
let rec existspk let let rec exists'(null) false exists'(decl (k',  , y)) p (y) || exists' (k') in exists' k(* this should be non-strict *)
(* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
(* Wed Aug  6 16:37:57 2003 -fp *)
(* !!! *)
let rec or(maybe,  , _) maybe or(_,  , maybe) maybe or(meta,  , _) meta or(_,  , meta) meta or(no,  , no) no(* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
let rec occursInExp(k,  , uni _) no occursInExp(k,  , pi (dP,  , v)) or (occursInDecP (k,  , dP),  , occursInExp (k + 1,  , v)) occursInExp(k,  , root (h,  , s)) occursInHead (k,  , h,  , occursInSpine (k,  , s)) occursInExp(k,  , lam (d,  , v)) or (occursInDec (k,  , d),  , occursInExp (k + 1,  , v)) occursInExp(k,  , fgnExp csfe) fold csfe (fun (u,  , dP) -> or (dP,  , (occursInExp (k,  , normalize (u,  , id))))) no(* no case for Redex, EVar, EClo *)
 occursInHead(k,  , bVar (k'),  , dP) if (k = k') then maybe else dP occursInHead(k,  , const _,  , dP) dP occursInHead(k,  , def _,  , dP) dP occursInHead(k,  , proj _,  , dP) dP occursInHead(k,  , fgnConst _,  , dP) dP occursInHead(k,  , skonst _,  , no) no occursInHead(k,  , skonst _,  , meta) meta occursInHead(k,  , skonst _,  , maybe) meta(* no case for FVar *)
 occursInSpine(_,  , nil) no occursInSpine(k,  , app (u,  , s)) or (occursInExp (k,  , u),  , occursInSpine (k,  , s))(* no case for SClo *)
 occursInDec(k,  , dec (_,  , v)) occursInExp (k,  , v) occursInDecP(k,  , (d,  , _)) occursInDec (k,  , d)(* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
(* optimize to have fewer traversals? -cs *)
(* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
let rec piDepend(dPV as ((d,  , no),  , v)) pi dPV piDepend(dPV as ((d,  , meta),  , v)) pi dPV piDepend((d,  , maybe),  , v) pi ((d,  , occursInExp (1,  , v)),  , v)(* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , pi ((d,  , maybe),  , v))(* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)
let rec raiseTerm(null,  , u) u raiseTerm(decl (g,  , d),  , u) raiseTerm (g,  , lam (d,  , u))(* collectExpW (G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)
(* Possible optimization: Calculate also the normal form of the term *)
let rec collectExpW(g,  , (uni l,  , s),  , k) k collectExpW(g,  , (pi ((d,  , _),  , v),  , s),  , k) collectExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , collectDec (g,  , (d,  , s),  , k)) collectExpW(g,  , (root (f as fVar (name,  , v,  , s'),  , s),  , s),  , k) if exists (eqFVar f) k then collectSpine (g,  , (s,  , s),  , k) else (* s' = ^|G| *)
collectSpine (g,  , (s,  , s),  , decl (collectExp (null,  , (v,  , id),  , k),  , fV (name,  , v))) collectExpW(g,  , (root (proj (l as lVar (ref nONE,  , sk,  , (l,  , t)),  , i),  , s),  , s),  , k) collectSpine (g,  , (s,  , s),  , collectBlock (g,  , blockSub (l,  , s),  , k)) collectExpW(g,  , (root (_,  , s),  , s),  , k) collectSpine (g,  , (s,  , s),  , k) collectExpW(g,  , (lam (d,  , u),  , s),  , k) collectExp (decl (g,  , decSub (d,  , s)),  , (u,  , dot1 s),  , collectDec (g,  , (d,  , s),  , k)) collectExpW(g,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , k) if exists (eqEVar x) k then collectSub (g,  , s,  , k) else let (* val _ = checkEmpty !cnstrs *)
let  in(* inefficient *)
let  in in collectSub (g,  , s,  , decl (k',  , eV (x))) collectExpW(g,  , (fgnExp csfe,  , s),  , k) fold csfe (fun (u,  , k) -> collectExp (g,  , (u,  , s),  , k)) k(* No other cases can occur due to whnf invariant *)
(* collectExp (G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
 collectExp(g,  , us,  , k) collectExpW (g,  , whnf us,  , k)(* collectSpine (G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
 collectSpine(g,  , (nil,  , _),  , k) k collectSpine(g,  , (sClo (s,  , s'),  , s),  , k) collectSpine (g,  , (s,  , comp (s',  , s)),  , k) collectSpine(g,  , (app (u,  , s),  , s),  , k) collectSpine (g,  , (s,  , s),  , collectExp (g,  , (u,  , s),  , k))(* collectDec (G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
 collectDec(g,  , (dec (_,  , v),  , s),  , k) collectExp (g,  , (v,  , s),  , k) collectDec(g,  , (bDec (_,  , (_,  , t)),  , s),  , k) collectSub (g,  , comp (t,  , s),  , k) collectDec(g,  , (nDec _,  , s),  , k) k(* collectSub (G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
 collectSub(g,  , shift _,  , k) k collectSub(g,  , dot (idx _,  , s),  , k) collectSub (g,  , s,  , k) collectSub(g,  , dot (exp (u),  , s),  , k) collectSub (g,  , s,  , collectExp (g,  , (u,  , id),  , k)) collectSub(g,  , dot (block b,  , s),  , k) collectSub (g,  , s,  , collectBlock (g,  , b,  , k))(* next case should be impossible *)
(*
      | collectSub (G, I.Dot (I.Undef, s), K) =
          collectSub (G, s, K)
    *)
(* collectBlock (G, B, K) where G |- B block *)
 collectBlock(g,  , lVar (ref (sOME b),  , sk,  , _),  , k) collectBlock (g,  , blockSub (b,  , sk),  , k) collectBlock(g,  , l as lVar (_,  , sk,  , (l,  , t)),  , k) if exists (eqLVar l) k then collectSub (g,  , comp (t,  , sk),  , k) else decl (collectSub (g,  , comp (t,  , sk),  , k),  , lV l)(* was: t in the two lines above, July 22, 2010, -fp -cs *)
(* | collectBlock (G, I.Bidx _, K) = K *)
(* should be impossible: Fronts of substitutions are never Bidx *)
(* Sat Dec  8 13:30:43 2001 -fp *)
(* collectCtx (G0, G, K) = (G0', K')
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars and FVars in G
    *)
let rec collectCtx(g0,  , null,  , k) (g0,  , k) collectCtx(g0,  , decl (g,  , d),  , k) let let  inlet  in in (decl (g0,  , d),  , k'')(* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)
let rec collectCtxs(g0,  , nil,  , k) k collectCtxs(g0,  , g :: gs,  , k) let let  in in collectCtxs (g0',  , gs,  , k')(* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
let rec abstractEVar(decl (k',  , eV (eVar (r',  , _,  , _,  , _))),  , depth,  , x as eVar (r,  , _,  , _,  , _)) if r = r' then bVar (depth + 1) else abstractEVar (k',  , depth + 1,  , x) abstractEVar(decl (k',  , _),  , depth,  , x) abstractEVar (k',  , depth + 1,  , x)(* abstractFVar (K, depth, F) = C'

       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
let rec abstractFVar(decl (k',  , fV (n',  , _)),  , depth,  , f as fVar (n,  , _,  , _)) if n = n' then bVar (depth + 1) else abstractFVar (k',  , depth + 1,  , f) abstractFVar(decl (k',  , _),  , depth,  , f) abstractFVar (k',  , depth + 1,  , f)(* abstractLVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
let rec abstractLVar(decl (k',  , lV (lVar (r',  , _,  , _))),  , depth,  , l as lVar (r,  , _,  , _)) if r = r' then bidx (depth + 1) else abstractLVar (k',  , depth + 1,  , l) abstractLVar(decl (k',  , _),  , depth,  , l) abstractLVar (k',  , depth + 1,  , l)(* abstractExpW (K, depth, (U, s)) = U'
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
let rec abstractExpW(k,  , depth,  , (u as uni (l),  , s)) u abstractExpW(k,  , depth,  , (pi ((d,  , p),  , v),  , s)) piDepend ((abstractDec (k,  , depth,  , (d,  , s)),  , p),  , abstractExp (k,  , depth + 1,  , (v,  , dot1 s))) abstractExpW(k,  , depth,  , (root (f as fVar _,  , s),  , s)) root (abstractFVar (k,  , depth,  , f),  , abstractSpine (k,  , depth,  , (s,  , s))) abstractExpW(k,  , depth,  , (root (proj (l as lVar _,  , i),  , s),  , s)) root (proj (abstractLVar (k,  , depth,  , l),  , i),  , abstractSpine (k,  , depth,  , (s,  , s))) abstractExpW(k,  , depth,  , (root (h,  , s),  , s)) root (h,  , abstractSpine (k,  , depth,  , (s,  , s))) abstractExpW(k,  , depth,  , (lam (d,  , u),  , s)) lam (abstractDec (k,  , depth,  , (d,  , s)),  , abstractExp (k,  , depth + 1,  , (u,  , dot1 s))) abstractExpW(k,  , depth,  , (x as eVar _,  , s)) root (abstractEVar (k,  , depth,  , x),  , abstractSub (k,  , depth,  , s,  , nil)) abstractExpW(k,  , depth,  , (fgnExp csfe,  , s)) apply csfe (fun u -> abstractExp (k,  , depth,  , (u,  , s)))(* abstractExp (K, depth, (U, s)) = U'

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
 abstractSub(k,  , depth,  , shift (k),  , s) if k < depth then abstractSub (k,  , depth,  , dot (idx (k + 1),  , shift (k + 1)),  , s) else (* k = depth *)
s abstractSub(k,  , depth,  , dot (idx (k),  , s),  , s) abstractSub (k,  , depth,  , s,  , app (root (bVar (k),  , nil),  , s)) abstractSub(k,  , depth,  , dot (exp (u),  , s),  , s) abstractSub (k,  , depth,  , s,  , app (abstractExp (k,  , depth,  , (u,  , id)),  , s))(* abstractSpine (K, depth, (S, s)) = S'
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
 abstractDec(k,  , depth,  , (dec (x,  , v),  , s)) dec (x,  , abstractExp (k,  , depth,  , (v,  , s)))(* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
       Above is now incorrect
       Sun Dec  1 22:36:50 2002 -fp
    *)
let rec abstractSOME(k,  , shift 0) shift (ctxLength (k)) abstractSOME(k,  , shift (n)) shift (ctxLength (k)) abstractSOME(k,  , dot (idx k,  , s)) dot (idx k,  , abstractSOME (k,  , s)) abstractSOME(k,  , dot (exp u,  , s)) dot (exp (abstractExp (k,  , 0,  , (u,  , id))),  , abstractSOME (k,  , s)) abstractSOME(k,  , dot (block (l as lVar _),  , s)) dot (block (abstractLVar (k,  , 0,  , l)),  , abstractSOME (k,  , s))(* I.Block (I.Bidx _) should be impossible as head of substitutions *)
(* abstractCtx (K, depth, G) = (G', depth')
       where G' = {{G}}_K

       Invariants:
       If G0 |- G ctx
       and K ||- G
       and |G0| = depth
       then {{K}}, G0 |- G' ctx
       and . ||- G'
       and |G0,G| = depth'
    *)
let rec abstractCtx(k,  , depth,  , null) (null,  , depth) abstractCtx(k,  , depth,  , decl (g,  , d)) let let  inlet  in in (decl (g',  , d'),  , depth' + 1)(* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)
let rec abstractCtxlist(k,  , depth,  , nil) nil abstractCtxlist(k,  , depth,  , g :: gs) let let  inlet  in in g' :: gs'(* dead code under new reconstruction -kw
    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
    fun getLevel (I.Uni _) = I.Kind
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
    fun checkType V =
        (case getLevel V
           of I.Type => ()
            | _ => raise Error "Typing ambiguous -- free type variable")
    *)
(* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
let rec abstractKPi(null,  , v) v abstractKPi(decl (k',  , eV (eVar (_,  , gX,  , vX,  , _))),  , v) let let  inlet  in(* enforced by reconstruction -kw
          val _ = checkType V'' *)
 in abstractKPi (k',  , pi ((dec (nONE,  , v''),  , maybe),  , v)) abstractKPi(decl (k',  , fV (name,  , v')),  , v) let let  in(* enforced by reconstruction -kw
          val _ = checkType V'' *)
 in abstractKPi (k',  , pi ((dec (sOME (name),  , v''),  , maybe),  , v)) abstractKPi(decl (k',  , lV (lVar (r,  , _,  , (l,  , t)))),  , v) let let  in in abstractKPi (k',  , pi ((bDec (nONE,  , (l,  , t')),  , maybe),  , v))(* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant:
       If   {{K}} |- U : V
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)
let rec abstractKLam(null,  , u) u abstractKLam(decl (k',  , eV (eVar (_,  , gX,  , vX,  , _))),  , u) let let  in in abstractKLam (k',  , lam (dec (nONE,  , abstractExp (k',  , 0,  , (v',  , id))),  , u)) abstractKLam(decl (k',  , fV (name,  , v')),  , u) abstractKLam (k',  , lam (dec (sOME (name),  , abstractExp (k',  , 0,  , (v',  , id))),  , u))let rec abstractKCtx(null) null abstractKCtx(decl (k',  , eV (eVar (_,  , gX,  , vX,  , _)))) let let  inlet  in(* enforced by reconstruction -kw
          val _ = checkType V'' *)
 in decl (abstractKCtx k',  , dec (nONE,  , v'')) abstractKCtx(decl (k',  , fV (name,  , v'))) let let  in(* enforced by reconstruction -kw
          val _ = checkType V'' *)
 in decl (abstractKCtx k',  , dec (sOME (name),  , v'')) abstractKCtx(decl (k',  , lV (lVar (r,  , _,  , (l,  , t))))) let let  in in decl (abstractKCtx k',  , bDec (nONE,  , (l,  , t')))(* abstractDecImp V = (k', V')   (* rename --cs  (see above) *)

       Invariant:
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)
let rec abstractDecImpv let let  inlet  in in (ctxLength k,  , abstractKPi (k,  , abstractExp (k,  , 0,  , (v,  , id))))(* abstractDef  (U, V) = (k', (U', V'))

       Invariant:
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |K|
    *)
let rec abstractDef(u,  , v) let let  inlet  in in (ctxLength k,  , (abstractKLam (k,  , abstractExp (k,  , 0,  , (u,  , id))),  , abstractKPi (k,  , abstractExp (k,  , 0,  , (v,  , id)))))let rec abstractSpineExt(s,  , s) let let  inlet  inlet  inlet  in in (g,  , s)(* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for some K
       then G0 |- G1',...,Gn' ctx for G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)
let rec abstractCtxs(gs) let let  inlet  in in (abstractKCtx (k),  , abstractCtxlist (k,  , 0,  , gs))(* closedDec (G, D) = true iff D contains no EVar or FVar *)
let rec closedDec(g,  , (dec (_,  , v),  , s)) match collectExp (g,  , (v,  , s),  , null) with null -> true _ -> falselet rec closedSub(g,  , shift _) true closedSub(g,  , dot (idx _,  , s)) closedSub (g,  , s) closedSub(g,  , dot (exp u,  , s)) (match collectExp (g,  , (u,  , id),  , null) with null -> closedSub (g,  , s) _ -> false)let rec closedExp(g,  , (u,  , s)) match collectExp (g,  , (u,  , id),  , null) with null -> true _ -> falselet rec closedCtxnull true closedCtx(decl (g,  , d)) closedCtx g && closedDec (g,  , (d,  , id))let rec closedFor(psi,  , true) true closedFor(psi,  , all ((d,  , _),  , f)) closedDEC (psi,  , d) && closedFor (decl (psi,  , d),  , f) closedFor(psi,  , ex ((d,  , _),  , f)) closedDec (coerceCtx psi,  , (d,  , id)) && closedFor (decl (psi,  , uDec d),  , f) closedDEC(psi,  , uDec d) closedDec (coerceCtx psi,  , (d,  , id)) closedDEC(psi,  , pDec (_,  , f,  , _,  , _)) closedFor (psi,  , f)let rec closedCTXnull true closedCTX(decl (psi,  , d)) closedCTX psi && closedDEC (psi,  , d)let rec evarsToK(nil) null evarsToK(x :: xs) decl (evarsToK (xs),  , eV (x))let rec kToEVars(null) nil kToEVars(decl (k,  , eV (x))) x :: kToEVars (k) kToEVars(decl (k,  , _)) kToEVars (k)(* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)
let rec collectEVars(g,  , us,  , xs) kToEVars (collectExp (g,  , us,  , evarsToK (xs)))let rec collectEVarsSpine(g,  , (s,  , s),  , xs) kToEVars (collectSpine (g,  , (s,  , s),  , evarsToK (xs)))(* for the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)
let rec collectPrg(_,  , p as eVar (psi,  , r,  , f,  , _,  , _,  , _),  , k) decl (k,  , pV p) collectPrg(psi,  , unit,  , k) k collectPrg(psi,  , pairExp (u,  , p),  , k) collectPrg (psi,  , p,  , collectExp (coerceCtx psi,  , (u,  , id),  , k))(* abstractPVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
let rec abstractPVar(decl (k',  , pV (eVar (_,  , r',  , _,  , _,  , _,  , _))),  , depth,  , p as eVar (_,  , r,  , _,  , _,  , _,  , _)) if r = r' then var (depth + 1) else abstractPVar (k',  , depth + 1,  , p) abstractPVar(decl (k',  , _),  , depth,  , p) abstractPVar (k',  , depth + 1,  , p)let rec abstractPrg(k,  , depth,  , x as eVar _) abstractPVar (k,  , depth,  , x) abstractPrg(k,  , depth,  , unit) unit abstractPrg(k,  , depth,  , pairExp (u,  , p)) pairExp (abstractExp (k,  , depth,  , (u,  , id)),  , abstractPrg (k,  , depth,  , p))let rec collectTomegaSub(shift 0) null collectTomegaSub(dot (exp u,  , t)) collectExp (null,  , (u,  , id),  , collectTomegaSub t) collectTomegaSub(dot (block b,  , t)) collectBlock (null,  , b,  , collectTomegaSub t) collectTomegaSub(dot (prg p,  , t)) collectPrg (null,  , p,  , collectTomegaSub t)let rec abstractOrder(k,  , depth,  , arg (us1,  , us2)) arg ((abstractExp (k,  , depth,  , us1),  , id),  , (abstractExp (k,  , depth,  , us2),  , id)) abstractOrder(k,  , depth,  , simul (os)) simul (map (fun o -> abstractOrder (k,  , depth,  , o)) os) abstractOrder(k,  , depth,  , lex (os)) lex (map (fun o -> abstractOrder (k,  , depth,  , o)) os)let rec abstractTC(k,  , depth,  , abs (d,  , tC)) abs (abstractDec (k,  , depth,  , (d,  , id)),  , abstractTC (k,  , depth,  , tC)) abstractTC(k,  , depth,  , conj (tC1,  , tC2)) conj (abstractTC (k,  , depth,  , tC1),  , abstractTC (k,  , depth,  , tC2)) abstractTC(k,  , depth,  , base (o)) base (abstractOrder (k,  , depth,  , o))let rec abstractTCOpt(k,  , depth,  , nONE) nONE abstractTCOpt(k,  , depth,  , sOME tC) sOME (abstractTC (k,  , depth,  , tC))let rec abstractMetaDec(k,  , depth,  , uDec d) uDec (abstractDec (k,  , depth,  , (d,  , id))) abstractMetaDec(k,  , depth,  , pDec (xx,  , f,  , tC1,  , tC2)) pDec (xx,  , abstractFor (k,  , depth,  , f),  , tC1,  , tC2)(* TC cannot contain free FVAR's or EVars'
            --cs  Fri Apr 30 13:45:50 2004 *)
(* Argument must be in normal form *)
 abstractFor(k,  , depth,  , true) true abstractFor(k,  , depth,  , all ((mD,  , q),  , f)) all ((abstractMetaDec (k,  , depth,  , mD),  , q),  , abstractFor (k,  , depth,  , f)) abstractFor(k,  , depth,  , ex ((d,  , q),  , f)) ex ((abstractDec (k,  , depth,  , (d,  , id)),  , q),  , abstractFor (k,  , depth,  , f)) abstractFor(k,  , depth,  , and (f1,  , f2)) and (abstractFor (k,  , depth,  , f1),  , abstractFor (k,  , depth,  , f2)) abstractFor(k,  , depth,  , world (w,  , f)) world (w,  , abstractFor (k,  , depth,  , f))let rec abstractPsi(null) null abstractPsi(decl (k',  , eV (eVar (_,  , gX,  , vX,  , _)))) let let  inlet  in(* enforced by reconstruction -kw
          val _ = checkType V'' *)
 in decl (abstractPsi k',  , uDec (dec (nONE,  , v''))) abstractPsi(decl (k',  , fV (name,  , v'))) let let  in(* enforced by reconstruction -kw
          val _ = checkType V'' *)
 in decl (abstractPsi k',  , uDec (dec (sOME (name),  , v''))) abstractPsi(decl (k',  , lV (lVar (r,  , _,  , (l,  , t))))) let let  in in decl (abstractPsi k',  , uDec (bDec (nONE,  , (l,  , t')))) abstractPsi(decl (k',  , pV (eVar (gX,  , _,  , fX,  , tC1,  , tC2,  , _)))) let let  inlet  inlet  in in decl (abstractPsi k',  , pDec (nONE,  , f',  , tC1,  , tC2))let rec abstractTomegaSubt let let  inlet  inlet  in in (psi,  , t') abstractTomegaSub'(k,  , depth,  , shift 0) shift depth abstractTomegaSub'(k,  , depth,  , dot (exp u,  , t)) (dot (exp (abstractExp (k,  , depth,  , (u,  , id))),  , abstractTomegaSub' (k,  , depth,  , t))) abstractTomegaSub'(k,  , depth,  , dot (block b,  , t)) (dot (block (abstractLVar (k,  , depth,  , b)),  , abstractTomegaSub' (k,  , depth,  , t))) abstractTomegaSub'(k,  , depth,  , dot (prg p,  , t)) (dot (prg (abstractPrg (k,  , depth,  , p)),  , abstractTomegaSub' (k,  , depth,  , t)))let rec abstractTomegaPrgp let let  inlet  inlet  in in (psi,  , p')(* just added to abstract over residual lemmas  -cs *)
(* Tomorrow: Make collection in program values a priority *)
(* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)
let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inend