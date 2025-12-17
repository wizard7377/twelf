Approx  Whnf WHNF     APPROX  struct (*! structure IntSyn = IntSyn' !*)
module let rec headConDec(const c) sgnLookup c headConDec(skonst c) sgnLookup c headConDec(def d) sgnLookup d headConDec(nSDef d) sgnLookup d headConDec(fgnConst (_,  , cd)) cd(* others impossible by invariant *)
(* The approximate language is based on the idea of erasure.  The
     erasure of a term is defined as follows:

       c- = c
       d- = d
       type- = type
       kind- = kind
       ({x:A} B)- = A- -> B-
       ([x:A] M)- = M-    
       (M N)- = M-

       x- undefined
       X- undefined

     Note that erasure is always defined on well-typed terms at type
     family or kind level.  Also, if G |- U1 = U2 : V and U1,U2 are at
     type family or kind level, then U1- and U2- are defined and
     equal.  We can define the approximate typing judgment
             
       G |- U ~:~ V
                  
     by replacing appeals to equality in the usual presentation of the
     LF type theory with appeals to

       G |- U1 = U2 ~:~ V,

     which is defined to mean
           G |- U1 ~:~ V  and  G |- U2 ~:~ V  and  U1- = U2-
                                                         
     This is a mutual recursion between the two judgments, just as for
     the standard LF type theory.

     There is also a typing judgment on approximate terms

       |- u : v

     defined in the obvious way.  If |- u : v : l then for any
     well-formed G there are most general U, V such that G |- U : V
     and U- = u and V- = v.  *)
(* The approximate language *)
type Unitype Exp(* Because approximate type reconstruction uses the pattern G |- U
     ~:~ V ~:~ L and universe unification on L, if U is to be an
     arbitrary input expression, there must be an internal universe
     Hyperkind such that |- Type ~:~ Kind ~:~ Hyperkind.  The
     Hyperkind universe is used only during the approximate phase of
     reconstruction.  The invariants established by
     ReconTerm.filterLevel ensure that Hyperkind will never appear
     elsewhere. *)
let  inlet  inlet  inlet rec newLVar() lVar (ref nONE)let rec newCVar() cVar (ref nONE)(* whnfUni (l) = l'
       where l = l' and l' is in whnf *)
let rec whnfUni(next l) (match whnfUni l with level i -> level (i + 1) l' -> next l') whnfUni(lVar (ref (sOME l))) whnfUni l whnfUnil l(* whnf (u) = u'
       where u = u' and u' is in whnf *)
let rec whnf(cVar (ref (sOME v))) whnf v whnfv v(* just a little list since these are only for printing errors *)
type VarEntrylet  inlet rec varReset() (varList := nil)let rec varLookupRefr find (fun ((cVar r',  , _,  , _),  , _) -> r = r') (! varList)let rec varLookupNamename find (fun (_,  , name') -> name = name') (! varList)let rec varInsert((u,  , v,  , l),  , name) (varList := ((u,  , v,  , l),  , name) :: (! varList))exception (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)
let rec getReplacementName(u as cVar r,  , v,  , l,  , allowed) (match varLookupRef r with sOME (_,  , name) -> name nONE -> let let  inlet  in(* others impossible by invariant *)
let rec tryi let let  in in match varLookupName name with nONE -> (varInsert ((u,  , v,  , l),  , name); name) sOME _ -> try (i + 1) in try 1)(* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)
let rec findByReplacementNamename (match varLookupName name with sOME (uVL,  , _) -> uVL(* must be in list by invariant *)
)(* converting exact terms to approximate terms *)
(* uniToApx (L) = L- *)
let rec uniToApx(type) type uniToApx(kind) kind(* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U ":" V = "hyperkind" *)
let rec expToApx(uni l) let let  in in (uni l',  , uni (whnfUni (next l'))) expToApx(pi ((dec (_,  , v1),  , _),  , v2)) let let  inlet  in in (arrow (v1',  , v2'),  , l') expToApx(root (fVar (name,  , _,  , _),  , _)) let let  in in (u,  , v) expToApx(root (h, (* Const/Def/NSDef *)
,  , _)) (const h,  , uni type) expToApx(redex (u,  , _)) expToApx u expToApx(lam (_,  , u)) expToApx u expToApx(eClo (u,  , _)) expToApx u(* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V ":" L = "hyperkind" *)
let rec classToApx(v) let let  inlet  in in (v',  , l'')(* exactToApx (U, V) = (U-, V-)
     if G |- U : V *)
let rec exactToApx(u,  , v) let let  in in match whnfUni l' with level 1(* Type *)
 -> (undefined,  , v',  , l') _(* Kind/Hyperkind *)
 -> let let  in in (u',  , v',  , l')(* constDefApx (d) = V-
     if |- d = V : type *)
let rec constDefApxd (match sgnLookup d with conDef (_,  , _,  , _,  , u,  , _,  , _,  , _) -> let let  in in v' abbrevDef (_,  , _,  , _,  , u,  , _,  , _) -> let let  in in v')(* converting approximate terms to exact terms *)
(* apxToUni (L-) = L *)
let rec apxToUniW(level 1) type apxToUniW(level 2) kind(* others impossible by invariant *)
let rec apxToUnil apxToUniW (whnfUni l)(* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)
let rec apxToClassW(g,  , uni l,  , _, (* Next L *)
,  , allowed) uni (apxToUni l) apxToClassW(g,  , arrow (v1,  , v2),  , l,  , allowed) let let  inlet  inlet  in in pi ((d,  , maybe),  , v2') apxToClassW(g,  , v as cVar r,  , l, (* Type or Kind *)
,  , allowed) let let  inlet  in in root (fVar (name,  , uni (apxToUni l),  , s),  , nil) apxToClassW(g,  , const h,  , l, (* Type *)
,  , allowed) root (h,  , newSpineVar (g,  , (conDecType (headConDec h),  , id)))(* Undefined case impossible *)
 apxToClass(g,  , v,  , l,  , allowed) apxToClassW (g,  , whnf v,  , l,  , allowed)(* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)
let rec apxToExactW(g,  , u,  , (pi ((d,  , _),  , v),  , s),  , allowed) let let  in in lam (d',  , apxToExact (decl (g,  , d'),  , u,  , (v,  , dot1 s),  , allowed)) apxToExactW(g,  , u,  , (uni l,  , s),  , allowed) apxToClass (g,  , u,  , uniToApx l,  , allowed) apxToExactW(g,  , u,  , vs as (root (fVar (name,  , _,  , _),  , _),  , s),  , allowed) let let  inlet  in in match whnfUni l with level 1 -> newEVar (g,  , eClo vs) level 2 -> (* U must be a CVar *)
let let  in(* NOTE: V' differs from Vs by a Shift *)
(* probably could avoid the following call by removing the
                  substitutions in Vs instead *)
let  inlet  in in root (fVar (name',  , v',  , s'),  , nil) apxToExactW(g,  , u,  , vs, (* an atomic type, not Def *)
,  , allowed) newEVar (g,  , eClo vs) apxToExact(g,  , u,  , vs,  , allowed) apxToExactW (g,  , u,  , whnfExpandDef vs,  , allowed)(* matching for the approximate language *)
exception (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)
let rec occurUniW(r,  , next l) occurUniW (r,  , l) occurUniW(r,  , lVar r') if r = r' then raise (unify "Level circularity") else () occurUniW(r,  , _) ()let rec occurUni(r,  , l) occurUniW (r,  , whnfUni l)(* matchUni (l1, l2) = ()
       iff l1<I> = l2<I> for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
let rec matchUniW(level i1,  , level i2) if i1 = i2 then () else raise (unify "Level clash") matchUniW(level i1,  , next l2) if i1 > 1 then matchUniW (level (i1 - 1),  , l2) else raise (unify "Level clash") matchUniW(next l1,  , level i2) if i2 > 1 then matchUniW (l1,  , level (i2 - 1)) else raise (unify "Level clash") matchUniW(next l1,  , next l2) matchUniW (l1,  , l2) matchUniW(lVar r1,  , l2 as lVar r2) if r1 = r2 then () else r1 := sOME l2 matchUniW(lVar r1,  , l2) (occurUniW (r1,  , l2); r1 := sOME l2) matchUniW(l1,  , lVar r2) (occurUniW (r2,  , l1); r2 := sOME l1)let rec matchUni(l1,  , l2) matchUniW (whnfUni l1,  , whnfUni l2)(* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)
let rec occurW(r,  , arrow (v1,  , v2)) (occur (r,  , v1); occur (r,  , v2)) occurW(r,  , cVar r') if r = r' then raise (unify "Type/kind variable occurrence") else () occurW(r,  , _) () occur(r,  , u) occurW (r,  , whnf u)(* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
let rec matchW(uni l1,  , uni l2) matchUni (l1,  , l2) matchW(v1 as const h1,  , v2 as const h2) (match (h1,  , h2) with (const (c1),  , const (c2)) -> if c1 = c2 then () else raise (unify "Type/kind constant clash") (def (d1),  , def (d2)) -> if d1 = d2 then () else match (constDefApx d1,  , constDefApx d2) (def (d1),  , _) -> match (constDefApx d1,  , v2) (_,  , def (d2)) -> match (v1,  , constDefApx d2)(* strictness is irrelevant to matching on approximate types *)
 (nSDef (d1),  , nSDef (d2)) -> if d1 = d2 then () else match (constDefApx d1,  , constDefApx d2) (nSDef (d1),  , _) -> match (constDefApx d1,  , v2) (_,  , nSDef (d2)) -> match (v1,  , constDefApx d2)(* others cannot occur by invariant *)
) matchW(arrow (v1,  , v2),  , arrow (v3,  , v4)) (try  with ; match (v2,  , v4)) matchW(v1 as arrow _,  , const (def (d2))) match (v1,  , constDefApx d2) matchW(const (def (d1)),  , v2 as arrow _) match (constDefApx d1,  , v2) matchW(v1 as arrow _,  , const (nSDef (d2))) match (v1,  , constDefApx d2) matchW(const (nSDef (d1)),  , v2 as arrow _) match (constDefApx d1,  , v2) matchW(cVar r1,  , u2 as cVar r2) if r1 = r2 then () else r1 := sOME u2 matchW(cVar r1,  , u2) (occurW (r1,  , u2); r1 := sOME u2) matchW(u1,  , cVar r2) (occurW (r2,  , u1); r2 := sOME u1) matchW_ raise (unify "Type/kind expression clash") match(u1,  , u2) matchW (whnf u1,  , whnf u2)let rec matchable(u1,  , u2) try  with let rec makeGroundUni(level _) false makeGroundUni(next l) makeGroundUni l makeGroundUni(lVar (ref (sOME l))) makeGroundUni l makeGroundUni(lVar (r as ref nONE)) (r := sOME (level 1); true)end