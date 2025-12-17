Whnf   WHNF  struct (*! structure IntSyn = IntSyn' !*)
(*
     Weak Head-Normal Form (whnf)

     whnf ::= (L, s) | (Pi DP. U, s) | (Root (#k(b), S))
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Root(fgnC,S), id) where fgnC is a foreign constant
            | (Lam D. U, s) | (X, s) where X is uninstantiated, X of base type
                                     during type reconstruction, X might have variable type
            | (FgnExp, id) where FgnExp is a foreign expression

     Normal Form (nf)

        UA ::= L | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) | Root(fgnC,SA) | Root (#k(b), S)
             | Lam DA. UA | FgnExp
        DA ::= x:UA
        SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     X[s] where X is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *)
open IntSyn (* exception Undefined *)
exception (* etaContract (U, s, n) = k'

       Invariant:
       if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
       then if   lam V1...lam Vn. U[s] =eta*=> k
            then k' = k
            and  G |- k' : Pi V1...Pi Vn. V [s]
            else Eta is raised
              (even if U[s] might be eta-reducible to some other expressions).
    *)
(* optimization(?): quick check w/o substitution first *)
let rec etaContract(root (bVar (k),  , s),  , s,  , n) (match bvarSub (k,  , s) with idx (k') -> if k' > n then (etaContract' (s,  , s,  , n); k' - n) else raise (eta) _ -> raise (eta)) etaContract(lam (d,  , u),  , s,  , n) etaContract (u,  , dot1 s,  , n + 1) etaContract(eClo (u,  , s'),  , s,  , n) etaContract (u,  , comp (s',  , s),  , n) etaContract(eVar (ref (sOME (u)),  , _,  , _,  , _),  , s,  , n) etaContract (u,  , s,  , n) etaContract(aVar (ref (sOME (u))),  , s,  , n) etaContract (u,  , s,  , n) etaContract_ raise (eta)(* Should fail: (c@S), (d@S), (F@S), X *)
(* Not treated (fails): U@S *)
(* Could weak head-normalize for more thorough checks *)
(* Impossible: L, Pi D.V *)
(* etaContract' (S, s, n) = R'

       Invariant:
       If  G |- s : G1    and  G1 |- S : V > W
       then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
            then ()
       else Eta is raised
    *)
 etaContract'(nil,  , s,  , 0) () etaContract'(app (u,  , s),  , s,  , n) if etaContract (u,  , s,  , 0) = n then etaContract' (s,  , s,  , n - 1) else raise (eta) etaContract'(sClo (s,  , s'),  , s,  , n) etaContract' (s,  , comp (s',  , s),  , n) etaContract'_ raise (eta)(* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
let rec dotEta(ft as idx _,  , s) dot (ft,  , s) dotEta(ft as exp (u),  , s) let let  in in dot (ft',  , s) dotEta(ft as undef,  , s) dot (ft,  , s)(* appendSpine ((S1, s1), (S2, s2)) = S'

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]
    *)
let rec appendSpine((nil,  , s1),  , ss2) sClo ss2 appendSpine((app (u1,  , s1),  , s1),  , ss2) app (eClo (u1,  , s1),  , appendSpine ((s1,  , s1),  , ss2)) appendSpine((sClo (s1,  , s1'),  , s1),  , ss2) appendSpine ((s1,  , comp (s1',  , s1)),  , ss2)(* whnfRedex ((U, s1), (S, s2)) = (U', s')

       Invariant:
       If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf
             G |- s2 : G2   G2 |- S : V2 > W2
             G |- V1 [s1] == V2 [s2] == V : L
       then  G |- s' : G',  G' |- U' : W'
       and   G |- W'[s'] == W2[s2] == W : L
       and   G |- U'[s'] == (U[s1] @ S[s2]) : W
       and   (U',s') whnf

       Effects: EVars may be lowered to base type.
    *)
let rec whnfRedex(us,  , (sClo (s,  , s2'),  , s2)) whnfRedex (us,  , (s,  , comp (s2',  , s2))) whnfRedex(us as (root r,  , s1),  , (nil,  , s2)) us whnfRedex((root (h1,  , s1),  , s1),  , (s2,  , s2)) (root (h1,  , appendSpine ((s1,  , s1),  , (s2,  , s2))),  , id) whnfRedex((lam (_,  , u1),  , s1),  , (app (u2,  , s),  , s2)) whnfRedex (whnf (u1,  , dotEta (frontSub (exp (u2),  , s2),  , s1)),  , (s,  , s2)) whnfRedex(us as (lam _,  , s1),  , _) us whnfRedex(us as (eVar _,  , s1),  , (nil,  , s2)) us whnfRedex(us as (x as eVar _,  , s1),  , ss2) (lowerEVar x; whnfRedex (whnf us,  , ss2)) whnfRedex(us as (aVar (ref (sOME u)),  , s1),  , ss2) whnfRedex ((u,  , s1),  , ss2) whnfRedex(us as (aVar (ref nONE),  , s1),  , ss2) us whnfRedex(us as (fgnExp _,  , _),  , _) us whnfRedex(us as (uni _,  , s1),  , _) us whnfRedex(us as (pi _,  , s1),  , _) us(* S2[s2] = Nil *)
(* Other cases impossible since (U,s1) whnf *)
(* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
 lowerEVar'(g,  , (pi ((d',  , _),  , v'),  , s')) let let  inlet  in in (x',  , lam (d'',  , u)) lowerEVar'(g,  , vs') let let  in in (x',  , x')(* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
 lowerEVar1(eVar (r,  , g,  , _,  , _),  , vs as (pi _,  , _)) let let  inlet  in in x' lowerEVar1(x,  , _) x(* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
 lowerEVar(x as eVar (r,  , g,  , v,  , ref nil)) lowerEVar1 (x,  , whnfExpandDef (v,  , id)) lowerEVar(eVar _) raise (error "Typing ambiguous -- constraint of functional type cannot be simplified")(* whnfRoot ((H, S), s) = (U', s')

       Invariant:
       If    G |- s : G1      G1 |- H : V
                              G1 |- S : V > W
       then  G |- s' : G'     G' |- U' : W'
       and   G |- W [s] = W' [s'] : L

       Effects: EVars may be instantiated when lowered
    *)
 whnfRoot((bVar (k),  , s),  , s) (match bvarSub (k,  , s) with idx (k) -> (root (bVar (k),  , sClo (s,  , s)),  , id) exp (u) -> whnfRedex (whnf (u,  , id),  , (s,  , s))) whnfRoot((proj (b as bidx _,  , i),  , s),  , s) (match blockSub (b,  , s) with b' as bidx (k) -> (root (proj (b',  , i),  , sClo (s,  , s)),  , id) b' as lVar _ -> whnfRoot ((proj (b',  , i),  , sClo (s,  , s)),  , id) inst l -> whnfRedex (whnf (nth (l,  , i - 1),  , id),  , (s,  , s))) whnfRoot((proj (lVar (ref (sOME b),  , sk,  , (l,  , t)),  , i),  , s),  , s) whnfRoot ((proj (blockSub (b,  , comp (sk,  , s)),  , i),  , sClo (s,  , s)),  , id) whnfRoot((proj (l as lVar (r,  , sk,  , (l,  , t)),  , i),  , s),  , s) (root (proj (lVar (r,  , comp (sk,  , s),  , (l,  , t)),  , i),  , sClo (s,  , s)),  , id) whnfRoot((fVar (name,  , v,  , s'),  , s),  , s) (root (fVar (name,  , v,  , comp (s',  , s)),  , sClo (s,  , s)),  , id) whnfRoot((nSDef (d),  , s),  , s) whnfRedex (whnf (constDef d,  , id),  , (s,  , s)) whnfRoot((h,  , s),  , s) (root (h,  , sClo (s,  , s)),  , id)(* whnf (U, s) = (U', s')

       Invariant:
       If    G |- s : G'    G' |- U : V
       then  G |- s': G''   G''|- U' : V'
       and   G |- V [s] == V' [s'] == V'' : L
       and   G |- U [s] == U' [s'] : V''
       and   (U', s') whnf
    *)
(*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
         Fails currently because appendSpine does not necessairly return a closure  -cs
         Advantage: in unify, abstract... the spine needn't be treated under id, but under s
    *)
 whnf(u as uni _,  , s) (u,  , s) whnf(u as pi _,  , s) (u,  , s) whnf(root r,  , s) whnfRoot (r,  , s) whnf(redex (u,  , s),  , s) whnfRedex (whnf (u,  , s),  , (s,  , s)) whnf(us as (lam _,  , s)) us whnf(aVar (ref (sOME u)),  , s) whnf (u,  , s) whnf(us as (aVar _,  , s)) us whnf(eVar (ref (sOME u),  , _,  , _,  , _),  , s) whnf (u,  , s) whnf(us as (eVar (r,  , _,  , root _,  , _),  , s)) us whnf(us as (eVar (r,  , _,  , uni _,  , _),  , s)) us whnf(us as (x as eVar (r,  , _,  , v,  , _),  , s)) (match whnf (v,  , id) with (pi _,  , _) -> (lowerEVar x; whnf us)(* possible opt: call lowerEVar1 *)
 _ -> us) whnf(eClo (u,  , s'),  , s) whnf (u,  , comp (s',  , s)) whnf(us as (fgnExp _,  , shift (0))) us whnf(us as (fgnExp csfe,  , s)) (apply csfe (fun u -> eClo (u,  , s)),  , id)(* expandDef (Root (Def (d), S), s) = (U' ,s')

       Invariant:
       If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                             .  |- d = U : V'
       then  G |- s' : G'    G' |- U' : W'
       and   G |- V' == V [s] : L
       and   G |- W' [s'] == W [s] == W'' : L
       and   G |- (U @ S) [s] == U' [s'] : W'
       and   (U', s') in whnf
    *)
 expandDef(root (def (d),  , s),  , s) whnfRedex (whnf (constDef (d),  , id),  , (s,  , s)) whnfExpandDefW(us as (root (def _,  , _),  , _)) whnfExpandDefW (expandDef us) whnfExpandDefWus us whnfExpandDefus whnfExpandDefW (whnf us)let rec newLoweredEVarW(g,  , (pi ((d,  , _),  , v),  , s)) let let  in in lam (d',  , newLoweredEVar (decl (g,  , d'),  , (v,  , dot1 s))) newLoweredEVarW(g,  , vs) newEVar (g,  , eClo vs) newLoweredEVar(g,  , vs) newLoweredEVarW (g,  , whnfExpandDef vs)let rec newSpineVarW(g,  , (pi ((dec (_,  , va),  , _),  , vr),  , s)) let let  in in app (x,  , newSpineVar (g,  , (vr,  , dotEta (exp (x),  , s)))) newSpineVarW(g,  , _) nil newSpineVar(g,  , vs) newSpineVarW (g,  , whnfExpandDef vs)let rec spineToSub(nil,  , s) s spineToSub(app (u,  , s),  , s) spineToSub (s,  , dotEta (exp (u),  , s))(* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1[s1] == W)
       then G |- V'[s'] = W
    *)
(* FIX: this is almost certainly mis-design -kw *)
let rec inferSpine((nil,  , _),  , vs) vs inferSpine((sClo (s,  , s'),  , s),  , vs) inferSpine ((s,  , comp (s',  , s)),  , vs) inferSpine((app (u,  , s),  , s1),  , (pi (_,  , v2),  , s2)) inferSpine ((s,  , s1),  , whnfExpandDef (v2,  , dot (exp (eClo (u,  , s1)),  , s2)))(* inferCon (C) = V  if C = c or C = d or C = sk and |- C : V *)
(* FIX: this is almost certainly mis-design -kw *)
let rec inferCon(const (cid)) constType (cid) inferCon(skonst (cid)) constType (cid) inferCon(def (cid)) constType (cid)(* etaExpand' (U, (V,s)) = U'

       Invariant :
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *)
(* quite inefficient -cs *)
(* FIX: this is almost certainly mis-design -kw *)
let rec etaExpand'(u,  , (root _,  , s)) u etaExpand'(u,  , (pi ((d,  , _),  , v),  , s)) lam (decSub (d,  , s),  , etaExpand' (redex (eClo (u,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , whnfExpandDef (v,  , dot1 s)))(* etaExpandRoot (Root(H, S)) = U' where H = c or H = d

       Invariant:
       If   G |- H @ S : V  where H = c or H = d
       then G |- U' : V
       and  G |- H @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *)
(* FIX: this is almost certainly mis-design -kw *)
let rec etaExpandRoot(u as root (h,  , s)) etaExpand' (u,  , inferSpine ((s,  , id),  , (inferCon (h),  , id)))(* whnfEta ((U, s1), (V, s2)) = ((U', s1'), (V', s2)')

       Invariant:
       If   G |- s1 : G1  G1 |- U : V1
       and  G |- s2 : G2  G2 |- V : L
       and  G |- V1[s1] == V[s2] : L

       then G |- s1' : G1'  G1' |- U' : V1'
       and  G |- s2' : G2'  G2' |- V' : L'
       and  G |- V1'[s1'] == V'[s2'] : L
       and (U', s1') is in whnf
       and (V', s2') is in whnf
       and (U', s1') == Lam x.U'' if V[s2] == Pi x.V''

       Similar to etaExpand', but without recursive expansion
    *)
(* FIX: this is almost certainly mis-design -kw *)
let rec whnfEta(us,  , vs) whnfEtaW (whnf us,  , whnf vs) whnfEtaW(usVs as (_,  , (root _,  , _))) usVs whnfEtaW(usVs as ((lam _,  , _),  , (pi _,  , _))) usVs whnfEtaW((u,  , s1),  , vs2 as (pi ((d,  , p),  , v),  , s2)) ((lam (decSub (d,  , s2),  , redex (eClo (u,  , comp (s1,  , shift)),  , app (root (bVar (1),  , nil),  , nil))),  , id),  , vs2)(* Invariant:

       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V
       then U [s] = U'
       and  U' in existential normal form

       If (U, s) contain no existential variables,
       then U' in normal formal
    *)
let rec normalizeExpus normalizeExpW (whnf us) normalizeExpW(u as uni (l),  , s) u normalizeExpW(pi (dP,  , u),  , s) pi (normalizeDecP (dP,  , s),  , normalizeExp (u,  , dot1 s)) normalizeExpW(u as root (h,  , s),  , s) root (h,  , normalizeSpine (s,  , s)) normalizeExpW(lam (d,  , u),  , s) lam (normalizeDec (d,  , s),  , normalizeExp (u,  , dot1 s)) normalizeExpW(us as (eVar _,  , s)) eClo us normalizeExpW(fgnExp csfe,  , s) apply csfe (fun u -> normalizeExp (u,  , s)) normalizeExpW(us as (aVar (ref (sOME (u))),  , s)) normalizeExpW (u,  , s) normalizeExpW(us as (aVar _,  , s)) (print "Normalize  AVAR\n"; raise (error "")) normalizeSpine(nil,  , s) nil normalizeSpine(app (u,  , s),  , s) app (normalizeExp (u,  , s),  , normalizeSpine (s,  , s)) normalizeSpine(sClo (s,  , s'),  , s) normalizeSpine (s,  , comp (s',  , s)) normalizeDec(dec (xOpt,  , v),  , s) dec (xOpt,  , normalizeExp (v,  , s)) normalizeDec(bDec (xOpt,  , (c,  , t)),  , s) bDec (xOpt,  , (c,  , normalizeSub (comp (t,  , s)))) normalizeDecP((d,  , p),  , s) (normalizeDec (d,  , s),  , p)(* dead code -fp *)
(* pre-Twelf 1.2 code walk Fri May  8 11:37:18 1998 *)
(* not any more --cs Wed Jun 19 13:59:56 EDT 2002 *)
 normalizeSub(s as shift _) s normalizeSub(dot (ft as idx _,  , s)) dot (ft,  , normalizeSub (s)) normalizeSub(dot (exp u,  , s)) dotEta (exp (normalizeExp (u,  , id)),  , normalizeSub s)let rec normalizeCtxnull null normalizeCtx(decl (g,  , d)) decl (normalizeCtx g,  , normalizeDec (d,  , id))(* invert s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
let rec inverts let let rec lookup(n,  , shift _,  , p) nONE lookup(n,  , dot (undef,  , s'),  , p) lookup (n + 1,  , s',  , p) lookup(n,  , dot (idx k,  , s'),  , p) if k = p then sOME n else lookup (n + 1,  , s',  , p)let rec invert''(0,  , si) si invert''(p,  , si) (match (lookup (1,  , s,  , p)) with sOME k -> invert'' (p - 1,  , dot (idx k,  , si)) nONE -> invert'' (p - 1,  , dot (undef,  , si)))let rec invert'(n,  , shift p) invert'' (p,  , shift n) invert'(n,  , dot (_,  , s')) invert' (n + 1,  , s') in invert' (0,  , s)(* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G    (* and t strsub *)
       then G' |- t : G  and G' subcontext of G
    *)
let rec strengthen(shift n, (* = 0 *)
,  , null) null strengthen(dot (idx k, (* k = 1 *)
,  , t),  , decl (g,  , d)) let let  in in (* G |- D dec *)
(* G' |- t' : G *)
(* G' |- D[t'] dec *)
decl (strengthen (t',  , g),  , decSub (d,  , t')) strengthen(dot (undef,  , t),  , decl (g,  , d)) strengthen (t,  , g) strengthen(shift n,  , g) strengthen (dot (idx (n + 1),  , shift (n + 1)),  , g)(* isId s = B

       Invariant:
       If   G |- s: G', s weakensub
       then B holds
            iff s = id, G' = G
    *)
let rec isId'(shift (k),  , k') (k = k') isId'(dot (idx (n),  , s'),  , k') n = k' && isId' (s',  , k' + 1) isId'_ falselet rec isIds isId' (s,  , 0)(* cloInv (U, w) = U[w^-1]

       Invariant:
       If G |- U : V
          G |- w : G'  w weakening subst
          U[w^-1] defined (without pruning or constraints)

       then G' |- U[w^-1] : V[w^-1]
       Effects: None
    *)
let rec cloInv(u,  , w) eClo (u,  , invert w)(* cloInv (s, w) = s o w^-1

       Invariant:
       If G |- s : G1
          G |- w : G2  s weakening subst
          s o w^-1 defined (without pruning or constraints)

       then G2 |- s o w^-1 : G1
       Effects: None
    *)
let rec compInv(s,  , w) comp (s,  , invert w)(* functions previously in the Pattern functor *)
(* eventually, they may need to be mutually recursive with whnf *)
(* isPatSub s = B

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
let rec isPatSub(shift (k)) true isPatSub(dot (idx (n),  , s)) let let rec checkBVar(shift (k)) (n <= k) checkBVar(dot (idx (n'),  , s)) n <> n' && checkBVar (s) checkBVar(dot (undef,  , s)) checkBVar (s) checkBVar_ false in checkBVar s && isPatSub s isPatSub(dot (undef,  , s)) isPatSub s isPatSub_ false(* Try harder, due to bug somewhere *)
(* Sat Dec  7 17:05:02 2002 -fp *)
(* false *)
(* below does not work, because the patSub is lost *)
(*
          let val (U', s') = whnf (U, id)
          in
            isPatSub (Dot (Idx (etaContract (U', s', 0)), s))
            handle Eta => false
          end
      | isPatSub _ = false
      *)
(* makePatSub s = SOME(s') if s is convertible to a patSub
                      NONE otherwise

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
let rec mkPatSub(s as shift (k)) s mkPatSub(dot (idx (n),  , s)) let let  inlet rec checkBVar(shift (k)) (n <= k) checkBVar(dot (idx (n'),  , s')) n <> n' && checkBVar (s') checkBVar(dot (undef,  , s')) checkBVar (s')let  in in dot (idx (n),  , s') mkPatSub(dot (undef,  , s)) dot (undef,  , mkPatSub s) mkPatSub(dot (exp (u),  , s)) let let  inlet  in(* may raise Eta *)
 in dot (idx (k),  , mkPatSub s) mkPatSub_ raise (eta)let rec makePatSub(s) try  with let  inlet  inlet  inexception let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inend