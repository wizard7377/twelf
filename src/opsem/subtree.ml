MemoTable  Conv CONV    Whnf WHNF    AbstractTabled ABSTRACTTABLED    Print PRINT     MEMOTABLE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
module (*! structure TableParam = TableParam !*)
(* ---------------------------------------------------------------------- *)
(* Linear substitution tree for linear terms *)
(* normalSubsts: key = int = nvar *)
(* property: linear *)
type NormalSubststype ExSubstslet  inlet  inlet  inlet rec isIds isEmpty s(* ---------------------------------------------------------------------- *)
type Ctxlet rec emptyCtx() Ctx ref []let rec copyl Ctx ref (! l)(* destructively updates L *)
let rec delete(x,  , l : Ctx) let let rec del(x,  , [],  , l) nONE del(x,  , ((h as (y,  , e)) :: l),  , l') if x = y then sOME ((y,  , e),  , (rev l') @ l) else del (x,  , l,  , h :: l') in match del (x,  , (! l),  , []) with nONE -> nONE sOME ((y,  , e),  , l') -> (l := l'; sOME ((y,  , e)))let rec member(x,  , l : Ctx) let let rec memb(x,  , []) nONE memb(x,  , (h as (y,  , e) :: l)) if x = y then sOME ((y,  , e)) else memb (x,  , l) in memb (x,  , (! l))let rec insertList(e,  , l) (l := (e :: (! l)); l)(* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
let rec ctxToEVarSub(null,  , s) s ctxToEVarSub(decl (g,  , dec (_,  , a)),  , s) let let  inlet  in in dot (exp (x),  , s')(* ---------------------------------------------------------------------- *)
(* Substitution Tree *)
(* it is only possible to distribute the evar-ctx because
     all evars occur exactly once! -- linear
     this allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
     *)
type Treelet rec makeTree() ref (node ((emptyCtx (),  , nid ()),  , []))let rec noChildrenc (c = [])type Retrievaltype CompSub(* Index array

     All type families have their own substitution tree and all substitution trees
     are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
     *)
let  inexception module module module module module exception exception exception let rec emptyAnswer() emptyAnsw ()let  inlet  intype Nvar(* index for normal variables *)
type Bvar(* index for bound variables *)
type Bdepth(* depth of locally bound variables *)
(* ------------------------------------------------------ *)
(* Auxiliary functions *)
let rec cidFromHead(const c) c cidFromHead(def c) clet rec dotn(0,  , s) s dotn(i,  , s) dotn (i - 1,  , dot1 s)let rec compose(null,  , g) g compose(decl (g,  , d),  , g') decl (compose (g,  , g'),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))let rec raiseType(null,  , u) u raiseType(decl (g,  , d),  , u) raiseType (g,  , lam (d,  , u))let rec ctxToAVarSub(g',  , null,  , s) s ctxToAVarSub(g',  , decl (d,  , dec (_,  , a)),  , s) let let  in in dot (exp (e),  , ctxToAVarSub (g',  , d,  , s)) ctxToAVarSub(g',  , decl (d,  , aDec (_,  , d)),  , s) let let  in in dot (exp (eClo (x,  , shift (~ d))),  , ctxToAVarSub (g',  , d,  , s))(* solveEqn' ((VarDef, s), G) = bool

     if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
      return true, if VarDefs are solvable
      false otherwise
      *)
let rec solveEqn'((trivial,  , s),  , g) true solveEqn'((unify (g',  , e1,  , n, (* evar *)
,  , eqns),  , s),  , g) let let  inlet  in in unifiable (g'',  , (n,  , s'),  , (e1,  , s')) && solveEqn' ((eqns,  , s),  , g)(* ------------------------------------------------------ *)
(*  Variable b    : bound variable
     Variable n    : index variable
     linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
     linear Spine S ::= p ; S | NIL
     indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
     indexed spines S_i ::= t ; S_i | NIL
     Types   A
     Context G : context for bound variables (bvars)
     (type information is stored in the context)
        G ::= . | G, x : A
        Set of all index variables:  N

        linear terms are approximately well-typed in G:  G |- p
        after erasing all typing dependencies.


        Let s be a path in the substitution tree such that
        s1 o s2 o .... o sn = s,



        Let N1 ... Nn be the path from the root N1 to the leaf Nn,
        and si the substitution associated with node Ni.

       IMAGE(sn) = empty
       s1 o s2 o ... o sn = s and IMAGE(s) = empty
       i.e. index variables are only internally used and no
       index variable is left.

       A linear term U (and an indexed term t) can be decomposed into a term t' together with
       a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
       and the following holds:

       If    N  ; G |- t
       then  N' ; G |- t'
             N  ; G |- s : N' ; G
             N  ; G |- t'[s]     and t'[s] = t

      if we have a linear term then N will be empty, but the same holds.

      In addition:
      all expressions in the index are closed and linear, i.e.
      an expression is first linearized before it is inserted into the index
      (this makes retrieving all axpressions from the index which unify with
      a given expression simpler, because we can omit the occurs check)

   *)
(* ---------------------------------------------------------------*)
(* nctr = |D| =  #index variables *)
let  inlet rec newNVar() (nctr := ! nctr + 1; nVar (! nctr))let rec equalDec(dec (_,  , u),  , dec (_,  , u')) conv ((u,  , id),  , (u',  , id)) equalDec(aDec (_,  , d),  , aDec (_,  , d')) (d = d') equalDec(_,  , _) false(* We require order of both eqn must be the same Sun Sep  8 20:37:48 2002 -bp *)
(* s = s' = I.id *)
let rec equalCtx(null,  , s,  , null,  , s') true equalCtx(decl (g,  , d),  , s,  , decl (g',  , d'),  , s') convDec ((d,  , s),  , (d',  , s')) && (equalCtx (g,  , dot1 s,  , g',  , dot1 s')) equalCtx(_,  , _,  , _,  , _) false(* in general, we need to carry around and build up a substitution *)
let rec equalEqn(trivial,  , trivial) true equalEqn(unify (g,  , x,  , n,  , eqn),  , (unify (g',  , x',  , n',  , eqn'))) equalCtx (g,  , id,  , g',  , id) && conv ((x,  , id),  , (x',  , id)) && conv ((n,  , id),  , (n',  , id)) && equalEqn (eqn,  , eqn') equalEqn(_,  , _) falselet rec equalSub(shift k,  , shift k') (k = k') equalSub(dot (f,  , s),  , dot (f',  , s')) equalFront (f,  , f') && equalSub (s,  , s') equalSub(dot (f,  , s),  , shift k) false equalSub(shift k,  , dot (f,  , s)) false equalFront(idx n,  , idx n') (n = n') equalFront(exp u,  , exp v) conv ((u,  , id),  , (v,  , id)) equalFront(undef,  , undef) truelet rec equalSub1(dot (ms,  , s),  , dot (ms',  , s')) equalSub (s,  , s')let rec equalCtx'(null,  , null) true equalCtx'(decl (dk,  , dec (_,  , a)),  , decl (d1,  , dec (_,  , a1))) (conv ((a,  , id),  , (a1,  , id)) && equalCtx' (dk,  , d1)) equalCtx'(decl (dk,  , aDec (_,  , d')),  , decl (d1,  , aDec (_,  , d))) ((d = d') && equalCtx' (dk,  , d1)) equalCtx'(_,  , _) false(* ---------------------------------------------------------------*)
let rec compareCtx(g,  , g') equalCtx' (g,  , g')(* ---------------------------------------------------------------*)
(* most specific linear common generalization *)
(* compatible (T, U) = (T', rho_u, rho_t) opt
    if T is an indexed term
       U is a linear term
       U and T share at least the top function symbol
   then
       T'[rho_u] = U and T'[rho_t] = T
   *)
let rec isExists(d,  , bVar k,  , d) member (k - d,  , d)let rec compHeads((d_1,  , const k),  , (d_2,  , const k')) (k = k') compHeads((d_1,  , def k),  , (d_2,  , def k')) (k = k') compHeads((d_1,  , bVar k),  , (d_2,  , bVar k')) (match isExists (0,  , bVar k,  , d_1) with nONE -> (k = k') sOME (x,  , dec) -> true) compHeads((d_1,  , bVar k),  , (d_2,  , h2)) (match isExists (0,  , bVar k,  , d_1) with nONE -> false sOME (x,  , dec) -> true) compHeads((d_1,  , h1),  , (d_2,  , h2)) falselet rec compatible'((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u) let let rec genNVar((rho_t,  , t),  , (rho_u,  , u)) (insert rho_t (! nctr + 1,  , t); insert rho_u (! nctr + 1,  , u); newNVar ())let rec genRoot(depth,  , t as root (h1 as const k,  , s1),  , u as root (const k',  , s2)) if (k = k') then let let  in in root (h1,  , s') else genNVar ((rho_t,  , t),  , (rho_u,  , u)) genRoot(depth,  , t as root (h1 as def k,  , s1),  , u as root (def k',  , s2)) if (k = k') then let let  in in root (h1,  , s') else genNVar ((rho_t,  , t),  , (rho_u,  , u)) genRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (bVar k',  , s2)) if (k > d) && (k' > d) then (* globally bound variable *)
let let  inlet  in in match (member (k1,  , d_t),  , member (k2,  , d_u)) with (nONE,  , nONE) -> if (k1 = k2) then try  with  else genNVar ((rho_t,  , t),  , (rho_u,  , u)) (sOME (x,  , dec1),  , sOME (x',  , dec2)) -> (* k, k' refer to the existential *)
if ((k1 = k2) && equalDec (dec1,  , dec2)) then (* they refer to the same existential variable *)
let (* this is unecessary -- since existential variables have the same type
                                and need to be fully applied in order, S1 = S2 *)
let  in in (delete (x,  , d_t); delete (x',  , d_u); insertList ((x,  , dec1),  , ds); root (h1,  , s')) else (* variant checking only *)
genNVar ((rho_t,  , t),  , (rho_u,  , u)) (_,  , _) -> genNVar ((rho_t,  , t),  , (rho_u,  , u)) else (* locally bound variables *)
if (k = k') then try  with  else genNVar ((rho_t,  , t),  , (rho_u,  , u)) genRoot(d,  , t as root (h1 as bVar k,  , s1),  , u as root (const k',  , s2)) genNVar ((rho_t,  , t),  , (rho_u,  , u)) genRoot(d,  , t as root (h1,  , s1),  , u as root (h2,  , s2)) genNVar ((rho_t,  , t),  , (rho_u,  , u)) genExp(d,  , t as nVar n,  , u as root (h,  , s)) (insert rho_u (n,  , u); t) genExp(d,  , t as root (h1,  , s1),  , u as root (h2,  , s2)) genRoot (d,  , root (h1,  , s1),  , root (h2,  , s2)) genExp(d,  , lam (d1 as dec (_,  , a1),  , t1),  , lam (d2 as dec (_,  , a2),  , u2)) let let  in in lam (d1,  , e) genExp(d,  , t,  , u) (print "genExp -- falls through?\n"; genNVar ((rho_t,  , t),  , (rho_u,  , u))) genSpine(d,  , nil,  , nil) nil genSpine(d,  , app (t,  , s1),  , app (u,  , s2)) let let  inlet  in in app (e,  , s') genSpine(d,  , nil,  , app (_,  , _)) raise (differentSpines) genSpine(d,  , app (_,  , _),  , nil) raise (differentSpines) genSpine(d,  , sClo (_,  , _),  , _) raise (differentSpines) genSpine(d,  , _,  , sClo (_,  , _)) raise (differentSpines)let  in in variant elet rec compatible((d_t,  , t as root (h1,  , s1)),  , (d_u,  , u as root (h2,  , s2)),  , ds,  , rho_t,  , rho_u) if compHeads ((d_t,  , h1),  , (d_u,  , h2)) then compatible' ((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u) else notCompatible compatible((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u) compatible' ((d_t,  , t),  , (d_u,  , u),  , ds,  , rho_t,  , rho_u)(* ---------------------------------------------------------------*)
(* compatibleSub(nsub_t, nsub_u) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have "approximately" the same type)

   *)
let rec compatibleSub((d_t,  , nsub_t),  , (d_u,  , nsub_u)) let let  inlet  inlet  inlet  inlet  in(* by invariant rho_t = empty, since nsub_t <= nsub_u *)
let  in in if isId (rho_t) then (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
((! choose) true; variantSub (d_r2,  , rho_u)) else ((* split -- asub is unchanged *)
(! choose) false; if isId (sigma) then noCompatibleSub else splitSub ((dsigma,  , sigma),  , (d_r1,  , rho_t),  , (d_r2,  , rho_u)))(* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
(* ---------------------------------------------------------------------- *)
let rec mkLeaf(ds,  , gR,  , n) leaf (ds,  , gR)let rec mkNode(node (_,  , children),  , dsigma,  , drho1,  , gR,  , drho2) node (dsigma,  , [ref (leaf (drho2,  , ref [gR])); ref (node (drho1,  , children))]) mkNode(leaf (c,  , gRlist),  , dsigma,  , drho1,  , gR2,  , drho2) node (dsigma,  , [ref (leaf (drho2,  , ref [gR2])); ref (leaf (drho1,  , gRlist))])(* ---------------------------------------------------------------------- *)
let rec compatibleCtx((g,  , eqn),  , []) nONE compatibleCtx((g,  , eqn),  , ((l',  , g',  , eqn',  , answRef',  , _,  , status') :: gRlist)) (if (equalCtx' (g,  , g') && equalEqn (eqn,  , eqn')) then sOME (l',  , answRef',  , status') else compatibleCtx ((g,  , eqn),  , gRlist))let rec compChild(n as leaf ((d_t,  , nsub_t),  , gList),  , (d_e,  , nsub_e)) compatibleSub ((d_t,  , nsub_t),  , (d_e,  , nsub_e)) compChild(n as node ((d_t,  , nsub_t),  , children'),  , (d_e,  , nsub_e)) compatibleSub ((d_t,  , nsub_t),  , (d_e,  , nsub_e))let rec findAllCandidates(g_r,  , children,  , ds) let let rec findAllCands(g_r,  , nil,  , (d_u,  , sub_u),  , vList,  , sList) (vList,  , sList) findAllCands(g_r,  , (x :: l),  , (d_u,  , sub_u),  , vList,  , sList) match compChild (! x,  , (d_u,  , sub_u)) with noCompatibleSub -> findAllCands (g_r,  , l,  , (d_u,  , sub_u),  , vList,  , sList) splitSub (dsigma,  , drho1,  , drho2) -> findAllCands (g_r,  , l,  , (d_u,  , sub_u),  , vList,  , ((x,  , (dsigma,  , drho1,  , drho2)) :: sList)) variantSub (drho2 as (d_r2,  , rho2)) -> findAllCands (g_r,  , l,  , (d_u,  , sub_u),  , ((x,  , drho2,  , id) :: vList),  , sList) in findAllCands (g_r,  , children,  , ds,  , nil,  , nil)(* ---------------------------------------------------------------------- *)
let rec divergingCtx(stage,  , g,  , gRlistRef) let let  in in exists (fun ((evar,  , l),  , g',  , _,  , _,  , stage',  , _) -> (stage = stage' && (l > (ctxLength (g'))))) (! gRlistRef)let rec eqHeads(const k,  , const k') (k = k') eqHeads(bVar k,  , bVar k') (k = k') eqHeads(def k,  , def k') (k = k') eqHeads(_,  , _) false(* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)
let rec eqTerm(root (h2,  , s2),  , (t as root (h,  , s),  , rho1)) if eqHeads (h2,  , h) then eqSpine (s2,  , (s,  , rho1)) else false eqTerm(t2,  , (nVar n,  , rho1)) (match (lookup rho1 n) with nONE -> false sOME (t1) -> eqTerm (t2,  , (t1,  , nid ()))) eqTerm(lam (d2,  , t2),  , (lam (d,  , t),  , rho1)) eqTerm (t2,  , (t,  , rho1)) eqTerm(_,  , (_,  , _)) false eqSpine(nil,  , (nil,  , rho1)) true eqSpine(app (t2,  , s2),  , (app (t,  , s),  , rho1)) eqTerm (t2,  , (t,  , rho1)) && eqSpine (s2,  , (s,  , rho1)) eqSpine(_,  , _) falselet rec divergingSub((ds,  , sigma),  , (dr1,  , rho1),  , (dr2,  , rho2)) exists rho2 (fun (n2,  , t2) -> exists sigma (fun (_,  , t) -> eqTerm (t2,  , (t,  , rho1))))(* ---------------------------------------------------------------------- *)
(* Insert via variant checking *)
(* insert' (N, (D, nsub), GR) = (f, callCheckResult)

     invariant:

       N is a substitution tree
       nsub is a normal substitution
       D contains all the existential variables in nsub
       GR = (G : bound variable context,
             eqn: residual equations
             answRef : ptr to answer list

     if there exists a path p in N s.t. p ~ nsub
      then
       f is the identity, and callCheckResult = RepeatedEntry(_,_,answRef)
     otherwise (f is a function which destructively updates N
                and once executed, will add a path p ~ nsub to N,
                 callCheckResult = NewEntry (answRef)

  *)
let rec insert(nref,  , (d_u,  , nsub_u),  , gR) let let rec insert'(n as leaf ((d,  , _),  , gRlistRef),  , (d_u,  , nsub_u),  , gR as ((evarl,  , l),  , g_r,  , eqn,  , answRef,  , stage,  , status)) (match compatibleCtx ((g_r,  , eqn),  , (! gRlistRef)) with nONE -> ((* compatible path -- but different ctx! *)
if ((! divHeuristic) && divergingCtx (stage,  , g_r,  , gRlistRef)) then ((* ctx are diverging --- force suspension *)
(fun () -> (gRlistRef := (gR :: (! gRlistRef)); answList := (answRef :: (! answList))),  , divergingEntry (id,  , answRef))) else (* compatible path (variant) -- ctx are different *)
(fun () -> (gRlistRef := (gR :: (! gRlistRef)); answList := (answRef :: (! answList))),  , newEntry (answRef))) sOME ((evarl',  , glength),  , answRef',  , status') -> ((* compatible path -- SAME ctx *)
((fun () -> ()),  , repeatedEntry ((id,  , id),  , answRef',  , status')))) insert'(n as node ((d,  , sub),  , children),  , (d_u,  , nsub_u),  , gR as (l,  , g_r,  , eqn,  , answRef,  , stage,  , status)) let let  inlet rec checkCandidates(nil,  , nil) ((* no child is compatible with nsub_u *)
(fun () -> (nref := node ((d,  , sub),  , (ref (leaf ((d_u,  , nsub_u),  , ref [gR]))) :: children); answList := (answRef :: (! answList))),  , newEntry (answRef))) checkCandidates(nil,  , ((childRef,  , (dsigma,  , drho1,  , drho2)) :: _)) if ((! divHeuristic) && divergingSub (dsigma,  , drho1,  , drho2)) then ((* substree divering -- splitting node *)
(fun () -> (childRef := mkNode ((! childRef),  , dsigma,  , drho1,  , gR,  , drho2); answList := (answRef :: (! answList))),  , divergingEntry (id,  , answRef))) else ((* split existing node *)
(fun () -> (childRef := mkNode ((! childRef),  , dsigma,  , drho1,  , gR,  , drho2); answList := (answRef :: (! answList))),  , newEntry (answRef))) checkCandidates(((childRef,  , drho2,  , asub) :: nil),  , _) insert (childRef,  , drho2,  , gR) checkCandidates(((childRef,  , drho2,  , asub) :: l),  , sCands) (match (insert (childRef,  , drho2,  , gR)) with (_,  , newEntry (answRef)) -> checkCandidates (l,  , sCands) (f,  , repeatedEntry (asub,  , answRef,  , status)) -> ((f,  , repeatedEntry (asub,  , answRef,  , status))) (f,  , divergingEntry (asub,  , answRef)) -> ((f,  , divergingEntry (asub,  , answRef)))) in checkCandidates (variantCand,  , splitCand) in insert' (! nref,  , (d_u,  , nsub_u),  , gR)(* ---------------------------------------------------------------------- *)
(* answer check and insert

     Invariant:
        D |- Pi G.U
          |- (Pi G.U)[s]
       .  |- s : D
       {{K}} are all the free variables in s
        D_k is the linear context of all free variables in {{K}}
        D_k |- s_k : D  and eqn
        D_k |- (Pi G.U)[s_k] and eqn

      answerCheck (G, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (G,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U
     *)
let rec answCheckVariant(s',  , answRef,  , o) let let rec member((d,  , sk),  , []) false member((d,  , sk),  , (((d1,  , s1),  , _) :: s)) if equalSub (sk,  , s1) && equalCtx' (d,  , d1) then true else member ((d,  , sk),  , s)let  in in if member ((dEVars,  , sk),  , solutions answRef) then repeated else (addSolution (((dEVars,  , sk),  , o),  , answRef); new)(* ---------------------------------------------------------------------- *)
let rec reset() (nctr := 1; modify (fun (n,  , tree) -> (n := 0; tree := ! (makeTree ()); answList := []; added := false; (n,  , tree))) indexArray)let rec makeCtx(n,  , null,  , dEVars : Ctx) n makeCtx(n,  , decl (g,  , d),  , dEVars : Ctx) (insertList ((n,  , d),  , dEVars); makeCtx (n + 1,  , g,  , dEVars))(* callCheck (a, DA, DE, G, U eqn) = callCheckResult

       invariant:
       DA, DE, G |- U
       a is the type family of U

       if U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
let rec callCheck(a,  , dAVars,  , dEVars,  , g,  , u,  , eqn,  , status) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in match result with (sf,  , newEntry (answRef)) -> (sf (); added := true; if ! chatter >= 5 then print "\t -- Add goal \n" else (); newEntry (answRef)) (_,  , repeatedEntry (s as (_,  , asub),  , answRef,  , status)) -> (if ! chatter >= 5 then print "\t -- Suspend goal\n" else (); repeatedEntry ((esub,  , asub),  , answRef,  , status)) (sf,  , divergingEntry (answRef)) -> (sf (); added := true; if ! chatter >= 5 then print "\t -- Add diverging goal\n" else (); divergingEntry (answRef))(* insertIntoSTre (a, DA, DE, G, U eqn) = Succeeds

       invariant:
       DA, DE, G |- U
       a is the type family of U

       U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
let rec insertIntoTree(a,  , dAVars,  , dEVars,  , g,  , u,  , eqn,  , answRef,  , status) let let  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  in in match result with (sf,  , newEntry (answRef)) -> (added := true; if ! chatter >= 5 then print "\t -- Add goal \n" else (); newEntry (answRef)) (_,  , repeatedEntry (asub,  , answRef,  , status)) -> (if ! chatter >= 5 then print "\t -- Suspend goal\n" else (); repeatedEntry (asub,  , answRef,  , status)) (sf,  , divergingEntry (answRef)) -> (sf (); added := true; if ! chatter >= 5 then print "\t -- Add diverging goal\n" else (); divergingEntry (answRef))let rec answCheck(s',  , answRef,  , o) answCheckVariant (s',  , answRef,  , o)let rec updateTable() let let rec update[]flag flag update(answRef :: aList)flag (let let  in in if (l = lookup (answRef)) then (* no new solutions were added in the previous stage *)
update aList flag else (* new solutions were added *)
(updateAnswLookup (l,  , answRef); update aList true))let  inlet  in in added := falserlet  inlet  inlet  inlet  inlet  inlet  in(* memberCtx ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t. V = V'[^n]
       then return true
         otherwise false
     *)
let rec memberCtx((g,  , v),  , g') let let rec memberCtx'((g,  , v),  , null,  , n) nONE memberCtx'((g,  , v),  , decl (g',  , d' as dec (_,  , v')),  , n) if conv ((v,  , id),  , (v',  , shift n)) then sOME (d') else memberCtx' ((g,  , v),  , g',  , n + 1) in memberCtx' ((g,  , v),  , g',  , 1)(* local *)
end