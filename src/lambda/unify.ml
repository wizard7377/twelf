Unify  Whnf WHNF    Trail TRAIL     UNIFY  struct (*! structure IntSyn = IntSyn' !*)
exception exception open IntSyn type Actiontype CActiontype FAction(* ? *)
type UnifTraillet  inlet rec copyCnstr[] [] copyCnstr(refC :: clist) (bindCnstr (refC,  , ! refC) :: copyCnstr clist)let rec copy(instantiate refU) (bindExp (refU,  , ! refU)) copy(instantiateBlock refB) (bindBlock (refB,  , ! refB)) copy(add (cnstrs as ref cnstrs)) (bindAdd (cnstrs,  , copyCnstr (! cnstrs))) copy(solve (cnstr,  , cnstr)) (fSolve (cnstr,  , cnstr,  , ! cnstr))let rec resetCnstr[] [] resetCnstr(bindCnstr (refC,  , cnstr) :: l) (refC := cnstr; (refC :: (resetCnstr l)))let rec reset(bindExp (refU,  , u)) (refU := u; instantiate refU) reset(bindBlock (refB,  , b)) (refB := b; instantiateBlock refB) reset(bindAdd (cnstrs,  , cActions)) (cnstrs := resetCnstr cActions; add cnstrs) reset(fSolve (refCnstr,  , cnstr,  , cnstr')) (refCnstr := cnstr'; solve (refCnstr,  , cnstr))let rec suspend() suspend (globalTrail,  , copy)let rec resumetrail resume (trail,  , globalTrail,  , reset)let rec undo(instantiate refU) (refU := nONE) undo(instantiateBlock refB) (refB := nONE) undo(add (cnstrs as ref (cnstr :: cnstrL))) (cnstrs := cnstrL) undo(solve (cnstr,  , cnstr)) (cnstr := cnstr)let rec reset() reset globalTraillet rec mark() mark globalTraillet rec unwind() unwind (globalTrail,  , undo)let rec addConstraint(cnstrs,  , cnstr) (cnstrs := cnstr :: (! cnstrs); log (globalTrail,  , add (cnstrs)))let rec solveConstraint(cnstr as ref (cnstr)) (cnstr := solved; log (globalTrail,  , solve (cnstr,  , cnstr)))(* Associate a constraint to an expression *)
(* delayExpW ((U, s), cnstr) = ()

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then
       the constraint cnstr is added to all the rigid EVar occurrences in U[s]
    *)
let rec delayExpW((u as uni (l),  , s1),  , _) () delayExpW((pi ((d,  , p),  , u),  , s),  , cnstr) (delayDec ((d,  , s),  , cnstr); delayExp ((u,  , dot1 s),  , cnstr)) delayExpW((root (h,  , s),  , s),  , cnstr) (delayHead (h,  , cnstr); delaySpine ((s,  , s),  , cnstr)) delayExpW((lam (d,  , u),  , s),  , cnstr) (delayDec ((d,  , s),  , cnstr); delayExp ((u,  , dot1 s),  , cnstr)) delayExpW((eVar (g,  , r,  , v,  , cnstrs),  , s),  , cnstr) addConstraint (cnstrs,  , cnstr) delayExpW((fgnExp csfe,  , s),  , cnstr) apply csfe (fun u -> delayExp ((u,  , s),  , cnstr))(* no other cases by invariant *)
(* delayExp ((U, s), cnstr) = ()
       as in delayExpCW, except that the argument may not be in whnf
    *)
 delayExp(us,  , cnstr) delayExpW (whnf us,  , cnstr)(* delayHead (H, s, rOccur) = ()

       Invariant:
       If   G' |- H : V
       and  G' |- s : G         s is a pattern substitution
       then
       the constraint cnstr is added to a total of n rigid EVar occurrences in H[s]
    *)
 delayHead(fVar (x,  , v,  , s'),  , cnstr) delayExp ((v,  , id),  , cnstr) delayHead(h,  , _) ()(* delaySpine ((S, s), cnstr) = ()

       Invariant:
       If   G' |- s : G    G |- S : V > W
       then      G  |- S' : V' > W'
       the constraint cnstr is added to all the rigid EVar occurrences in S[s]
    *)
 delaySpine((nil,  , s),  , cnstr) () delaySpine((app (u,  , s),  , s),  , cnstr) (delayExp ((u,  , s),  , cnstr); delaySpine ((s,  , s),  , cnstr)) delaySpine((sClo (s,  , s'),  , s),  , cnstr) delaySpine ((s,  , comp (s',  , s)),  , cnstr)(* delayDec see delayExp *)
 delayDec((dec (name,  , v),  , s),  , cnstr) delayExp ((v,  , s),  , cnstr)let  inlet rec resetAwakenCnstrs() (awakenCnstrs := nil)let rec nextCnstr() match ! awakenCnstrs with nil -> nONE (cnstr :: cnstrL) -> (awakenCnstrs := cnstrL; sOME (cnstr))(* Instantiating EVars  *)
let rec instantiateEVar(refU,  , v,  , cnstrL) (refU := sOME (v); log (globalTrail,  , instantiate (refU)); awakenCnstrs := cnstrL @ ! awakenCnstrs)(* Instantiating LVars  *)
let rec instantiateLVar(refB,  , b) (refB := sOME (b); log (globalTrail,  , instantiateBlock (refB)))(* local *)
(* intersection (s1, s2) = s'
       s' = s1 /\ s2 (see JICSLP'96)

       Invariant:
       If   G |- s1 : G'    s1 patsub
       and  G |- s2 : G'    s2 patsub
       then G |- s' : G'' for some G''
       and  s' patsub
    *)
let rec intersection(dot (idx (k1),  , s1),  , dot (idx (k2),  , s2)) if (k1 = k2) then dot1 (intersection (s1,  , s2)) else comp (intersection (s1,  , s2),  , shift) intersection(s1 as dot _,  , shift (n2)) intersection (s1,  , dot (idx (n2 + 1),  , shift (n2 + 1))) intersection(shift (n1),  , s2 as dot _) intersection (dot (idx (n1 + 1),  , shift (n1 + 1)),  , s2) intersection(shift _,  , shift _) id(* both substitutions are the same number of shifts by invariant *)
(* all other cases impossible for pattern substitutions *)
(* weakenSub (G1, s, ss) = w'

       Invariant:
       If    G |- s : G1       (* s patsub *)
       and   G2 |- ss : G      (* ss strsub *)
       then  G1 |- w' : G1'    (* w' weaksub *)

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
    *)
let rec weakenSub(g,  , shift n,  , ss) if n < ctxLength g then weakenSub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , ss) else id weakenSub(g,  , dot (idx n,  , s'),  , ss) (match bvarSub (n,  , ss) with undef -> comp (weakenSub (g,  , s',  , ss),  , shift) idx _ -> dot1 (weakenSub (g,  , s',  , ss))) weakenSub(g,  , dot (undef,  , s'),  , ss) comp (weakenSub (g,  , s',  , ss),  , shift)(* invert (G, (U, s), ss, rOccur) = U[s][ss]

       G |- s : G'   G' |- U : V  (G |- U[s] : V[s])
       G'' |- ss : G

       Effect: raises NotInvertible if U[s][ss] does not exist
               or rOccurs occurs in U[s]
               does NOT prune EVars in U[s] according to ss; fails instead
    *)
let rec invertExp(g,  , us,  , ss,  , rOccur) invertExpW (g,  , whnf us,  , ss,  , rOccur) invertExpW(g,  , (u as uni _,  , s),  , _,  , _) u invertExpW(g,  , (pi ((d,  , p),  , v),  , s),  , ss,  , rOccur) pi ((invertDec (g,  , (d,  , s),  , ss,  , rOccur),  , p),  , invertExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , dot1 ss,  , rOccur)) invertExpW(g,  , (lam (d,  , v),  , s),  , ss,  , rOccur) lam (invertDec (g,  , (d,  , s),  , ss,  , rOccur),  , invertExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , dot1 ss,  , rOccur)) invertExpW(g,  , (root (h,  , s),  , s, (* = id *)
),  , ss,  , rOccur) root (invertHead (g,  , h,  , ss,  , rOccur),  , invertSpine (g,  , (s,  , s),  , ss,  , rOccur)) invertExpW(g,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , ss,  , rOccur) if (rOccur = r) then raise (notInvertible) else if isPatSub (s) then let let  in in if isId w then eClo (x,  , comp (s,  , ss)) else raise (notInvertible) else (* s not patsub *)
(* invertExp may raise NotInvertible *)
eClo (x,  , invertSub (g,  , s,  , ss,  , rOccur)) invertExpW(g,  , (fgnExp csfe,  , s),  , ss,  , rOccur) apply csfe (fun u -> invertExp (g,  , (u,  , s),  , ss,  , rOccur))(* other cases impossible since (U,s1) whnf *)
 invertDec(g,  , (dec (name,  , v),  , s),  , ss,  , rOccur) dec (name,  , invertExp (g,  , (v,  , s),  , ss,  , rOccur)) invertSpine(g,  , (nil,  , s),  , ss,  , rOccur) nil invertSpine(g,  , (app (u,  , s),  , s),  , ss,  , rOccur) app (invertExp (g,  , (u,  , s),  , ss,  , rOccur),  , invertSpine (g,  , (s,  , s),  , ss,  , rOccur)) invertSpine(g,  , (sClo (s,  , s'),  , s),  , ss,  , rOccur) invertSpine (g,  , (s,  , comp (s',  , s)),  , ss,  , rOccur) invertHead(g,  , bVar k,  , ss,  , rOccur) (match (bvarSub (k,  , ss)) with undef -> raise (notInvertible) idx k' -> bVar k') invertHead(g,  , h as const _,  , ss,  , rOccur) h invertHead(g,  , proj (b as bidx k,  , i),  , ss,  , rOccur) (match blockSub (b,  , ss) with bidx (k') -> proj (bidx (k'),  , i)) invertHead(g,  , h as proj (lVar (r,  , sk,  , (l,  , t)),  , i),  , ss,  , rOccur) (invertSub (g,  , t,  , id,  , rOccur); h) invertHead(g,  , h as skonst _,  , ss,  , rOccur) h invertHead(g,  , h as def _,  , ss,  , rOccur) h invertHead(g,  , fVar (x,  , v,  , s'),  , ss,  , rOccur) (invertExp (g,  , (v,  , id),  , id,  , rOccur); (* why G here? -fp !!! *)
fVar (x,  , v,  , comp (s',  , ss))) invertHead(g,  , h as fgnConst _,  , ss,  , rOccur) h(* pruneSub never allows pruning OUTDATED *)
(* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
 invertSub(g,  , s as shift (n),  , ss,  , rOccur) if n < ctxLength (g) then invertSub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , ss,  , rOccur) else comp (s,  , ss) invertSub(g,  , dot (idx (n),  , s'),  , ss,  , rOccur) (match bvarSub (n,  , ss) with undef -> raise (notInvertible) ft -> dot (ft,  , invertSub (g,  , s',  , ss,  , rOccur))) invertSub(g,  , dot (exp (u),  , s'),  , ss,  , rOccur) dot (exp (invertExp (g,  , (u,  , id),  , ss,  , rOccur)),  , invertSub (g,  , s',  , ss,  , rOccur))(* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
(* By invariant, all EVars X[s] are such that s is defined everywhere *)
(* Pruning establishes and maintains this invariant *)
(* invertCtx does not appear to be necessary *)
(*
    and invertCtx (Shift n, Null, rOccur) = Null
      | invertCtx (Dot (Idx k, t), Decl (G, D), rOccur) =
        let
          val t' = comp (t, invShift)
          val D' = invertDec (G, (D, id), t', rOccur)
        in
          Decl (invertCtx (t', G, rOccur), D')
        end
      | invertCtx (Dot (Undef, t), Decl (G, d), rOccur) =
          invertCtx (t, G, rOccur)
      | invertCtx (Shift n, G, rOccur) =
          invertCtx (Dot (Idx (n+1), Shift (n+1)), G, rOccur)
    *)
(* prune (G, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'
       !!! i would say
       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Unify if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
let rec pruneExp(g,  , us,  , ss,  , rOccur) pruneExpW (g,  , whnf us,  , ss,  , rOccur) pruneExpW(g,  , (u as uni _,  , s),  , _,  , _) u pruneExpW(g,  , (pi ((d,  , p),  , v),  , s),  , ss,  , rOccur) pi ((pruneDec (g,  , (d,  , s),  , ss,  , rOccur),  , p),  , pruneExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , dot1 ss,  , rOccur)) pruneExpW(g,  , (lam (d,  , v),  , s),  , ss,  , rOccur) lam (pruneDec (g,  , (d,  , s),  , ss,  , rOccur),  , pruneExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , dot1 ss,  , rOccur)) pruneExpW(g,  , (root (h,  , s),  , s, (* = id *)
),  , ss,  , rOccur) root (pruneHead (g,  , h,  , ss,  , rOccur),  , pruneSpine (g,  , (s,  , s),  , ss,  , rOccur)) pruneExpW(g,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , ss,  , rOccur) if (rOccur = r) then raise (unify "Variable occurrence") else if isPatSub (s) then let let  in in if isId w then eClo (x,  , comp (s,  , ss)) else let let  in(* val V' = EClo (V, wi) *)
let  in(* val GY = Whnf.strengthen (wi, GX) *)
let  in(* shortcut on GY possible by invariant on GX and V[s]? -fp *)
(* could optimize by checking for identity subst *)
let  inlet  inlet  in in eClo (yw,  , comp (s,  , ss)) else (* s not patsub *)
(try  with ) pruneExpW(g,  , (fgnExp csfe,  , s),  , ss,  , rOccur) apply csfe (fun u -> pruneExp (g,  , (u,  , s),  , ss,  , rOccur)) pruneExpW(g,  , ((x as aVar _),  , s),  , ss,  , rOccur) raise (unify "Left-over AVar")(* other cases impossible since (U,s1) whnf *)
 pruneDec(g,  , (dec (name,  , v),  , s),  , ss,  , rOccur) dec (name,  , pruneExp (g,  , (v,  , s),  , ss,  , rOccur)) pruneDec(g,  , (nDec x,  , _),  , _,  , _) nDec x(* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
 pruneSpine(g,  , (nil,  , s),  , ss,  , rOccur) nil pruneSpine(g,  , (app (u,  , s),  , s),  , ss,  , rOccur) app (pruneExp (g,  , (u,  , s),  , ss,  , rOccur),  , pruneSpine (g,  , (s,  , s),  , ss,  , rOccur)) pruneSpine(g,  , (sClo (s,  , s'),  , s),  , ss,  , rOccur) pruneSpine (g,  , (s,  , comp (s',  , s)),  , ss,  , rOccur) pruneHead(g,  , bVar k,  , ss,  , rOccur) (match (bvarSub (k,  , ss)) with undef -> raise (unify "Parameter dependency") idx k' -> bVar k') pruneHead(g,  , h as const _,  , ss,  , rOccur) h pruneHead(g,  , proj (b as bidx k,  , i),  , ss,  , rOccur) (match blockSub (b,  , ss) with bidx (k') -> proj (bidx (k'),  , i)) pruneHead(g,  , h as proj (lVar (r,  , sk,  , (l,  , t)),  , i),  , ss,  , rOccur) (pruneSub (g,  , t,  , id,  , rOccur); h) pruneHead(g,  , h as skonst _,  , ss,  , rOccur) h pruneHead(g,  , h as def _,  , ss,  , rOccur) h pruneHead(g,  , fVar (x,  , v,  , s'),  , ss,  , rOccur) (pruneExp (g,  , (v,  , id),  , id,  , rOccur); (* why G here? -fp !!! *)
fVar (x,  , v,  , comp (s',  , ss))) pruneHead(g,  , h as fgnConst _,  , ss,  , rOccur) h(* pruneSub never allows pruning OUTDATED *)
(* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
 pruneSub(g,  , s as shift (n),  , ss,  , rOccur) if n < ctxLength (g) then pruneSub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , ss,  , rOccur) else comp (s,  , ss) pruneSub(g,  , dot (idx (n),  , s'),  , ss,  , rOccur) (match bvarSub (n,  , ss) with undef -> raise (unify "Not prunable") ft -> dot (ft,  , pruneSub (g,  , s',  , ss,  , rOccur))) pruneSub(g,  , dot (exp (u),  , s'),  , ss,  , rOccur) dot (exp (pruneExp (g,  , (u,  , id),  , ss,  , rOccur)),  , pruneSub (g,  , s',  , ss,  , rOccur))(* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
(* By invariant, all EVars X[s] are such that s is defined everywhere *)
(* Pruning establishes and maintains this invariant *)
 pruneCtx(shift n,  , null,  , rOccur) null pruneCtx(dot (idx k,  , t),  , decl (g,  , d),  , rOccur) let let  inlet  in in decl (pruneCtx (t',  , g,  , rOccur),  , d') pruneCtx(dot (undef,  , t),  , decl (g,  , d),  , rOccur) pruneCtx (t,  , g,  , rOccur) pruneCtx(shift n,  , g,  , rOccur) pruneCtx (dot (idx (n + 1),  , shift (n + 1)),  , g,  , rOccur)(* unifyExpW (G, (U1, s1), (U2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, U1, s2, U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
let rec unifyExpW(g,  , us1 as (fgnExp csfe1,  , _),  , us2) (match (apply csfe1 (g,  , eClo us2)) with (succeed residualL) -> let let rec execResidual(assign (g,  , eVar (r,  , _,  , _,  , cnstrs),  , w,  , ss)) let let  in in instantiateEVar (r,  , w',  , ! cnstrs) execResidual(delay (u,  , cnstr)) delayExp ((u,  , id),  , cnstr) in app execResidual residualL fail -> raise (unify "Foreign Expression Mismatch")) unifyExpW(g,  , us1,  , us2 as (fgnExp csfe2,  , _)) (match (apply csfe2 (g,  , eClo us1)) with (succeed opL) -> let let rec execOp(assign (g,  , eVar (r,  , _,  , _,  , cnstrs),  , w,  , ss)) let let  in in instantiateEVar (r,  , w',  , ! cnstrs) execOp(delay (u,  , cnstr)) delayExp ((u,  , id),  , cnstr) in app execOp opL fail -> raise (unify "Foreign Expression Mismatch")) unifyExpW(g,  , (uni (l1),  , _),  , (uni (l2),  , _)) () unifyExpW(g,  , us1 as (root (h1,  , s1),  , s1),  , us2 as (root (h2,  , s2),  , s2)) (match (h1,  , h2) with (bVar (k1),  , bVar (k2)) -> if (k1 = k2) then unifySpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (unify "Bound variable clash") (const (c1),  , const (c2)) -> if (c1 = c2) then unifySpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (unify "Constant clash") (proj (b1,  , i1),  , proj (b2,  , i2)) -> if (i1 = i2) then (unifyBlock (g,  , b1,  , b2); unifySpine (g,  , (s1,  , s1),  , (s2,  , s2))) else raise (unify "Global parameter clash") (skonst (c1),  , skonst (c2)) -> if (c1 = c2) then unifySpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (unify "Skolem constant clash") (fVar (n1,  , _,  , _),  , fVar (n2,  , _,  , _)) -> if (n1 = n2) then unifySpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (unify "Free variable clash") (def (d1),  , def (d2)) -> if (d1 = d2) then (* because of strict *)
unifySpine (g,  , (s1,  , s1),  , (s2,  , s2)) else (*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
unifyDefDefW (g,  , us1,  , us2)(* four new cases for defined constants *)
 (def (d1),  , const (c2)) -> (match defAncestor d1 with anc (_,  , _,  , nONE) -> (* conservative *)
unifyExpW (g,  , expandDef us1,  , us2) anc (_,  , _,  , sOME (c1)) -> if (c1 = c2) then unifyExpW (g,  , expandDef us1,  , us2) else raise (unify "Constant clash")) (const (c1),  , def (d2)) -> (match defAncestor d2 with anc (_,  , _,  , nONE) -> (* conservative *)
unifyExpW (g,  , us1,  , expandDef us2) anc (_,  , _,  , sOME (c2)) -> if (c1 = c2) then unifyExpW (g,  , us1,  , expandDef us2) else raise (unify "Constant clash")) (def (d1),  , bVar (k2)) -> raise (unify "Head mismatch")(* due to strictness! *)
 (bVar (k1),  , def (d2)) -> raise (unify "Head mismatch")(* due to strictness! *)
(* next two cases for def/fgn, fgn/def *)
 (def (d1),  , _) -> unifyExpW (g,  , expandDef us1,  , us2) (_,  , def (d2)) -> unifyExpW (g,  , us1,  , expandDef us2) (fgnConst (cs1,  , conDec (n1,  , _,  , _,  , _,  , _,  , _)),  , fgnConst (cs2,  , conDec (n2,  , _,  , _,  , _,  , _,  , _))) -> (* we require unique string representation of external constants *)
if (cs1 = cs2) && (n1 = n2) then () else raise (unify "Foreign Constant clash") (fgnConst (cs1,  , conDef (n1,  , _,  , _,  , w1,  , _,  , _,  , _)),  , fgnConst (cs2,  , conDef (n2,  , _,  , _,  , v,  , w2,  , _,  , _))) -> if (cs1 = cs2) && (n1 = n2) then () else unifyExp (g,  , (w1,  , s1),  , (w2,  , s2)) (fgnConst (_,  , conDef (_,  , _,  , _,  , w1,  , _,  , _,  , _)),  , _) -> unifyExp (g,  , (w1,  , s1),  , us2) (_,  , fgnConst (_,  , conDef (_,  , _,  , _,  , w2,  , _,  , _,  , _))) -> unifyExp (g,  , us1,  , (w2,  , s2)) _ -> raise (unify "Head mismatch")) unifyExpW(g,  , (pi ((d1,  , _),  , u1),  , s1),  , (pi ((d2,  , _),  , u2),  , s2)) (unifyDec (g,  , (d1,  , s1),  , (d2,  , s2)); unifyExp (decl (g,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , (u2,  , dot1 s2))) unifyExpW(g,  , us1 as (pi (_,  , _),  , _),  , us2 as (root (def _,  , _),  , _)) unifyExpW (g,  , us1,  , expandDef (us2)) unifyExpW(g,  , us1 as (root (def _,  , _),  , _),  , us2 as (pi (_,  , _),  , _)) unifyExpW (g,  , expandDef (us1),  , us2) unifyExpW(g,  , (lam (d1,  , u1),  , s1),  , (lam (d2,  , u2),  , s2)) unifyExp (decl (g,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , (u2,  , dot1 s2)) unifyExpW(g,  , (lam (d1,  , u1),  , s1),  , (u2,  , s2)) unifyExp (decl (g,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , (redex (eClo (u2,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , dot1 s2)) unifyExpW(g,  , (u1,  , s1),  , (lam (d2,  , u2),  , s2)) unifyExp (decl (g,  , decSub (d2,  , s2)),  , (redex (eClo (u1,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , dot1 s1),  , (u2,  , dot1 s2)) unifyExpW(g,  , us1 as (u1 as eVar (r1,  , g1,  , v1,  , cnstrs1),  , s1),  , us2 as (u2 as eVar (r2,  , g2,  , v2,  , cnstrs2),  , s2)) if r1 = r2 then if isPatSub (s1) then if isPatSub (s2) then let let  in(* compute ss' directly? *)
 in (* without the next optimization, bugs/hangs/sources.cfg
                     would gets into an apparent infinite loop
                     Fri Sep  5 20:23:27 2003 -fp
                  *)
if isId s'(* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
 then ()(* X[s] = X[s] *)
 else let let  inlet  in(* invertExp ((V1, id), s', ref NONE) *)
let  in in instantiateEVar (r1,  , eClo (newEVar (g1',  , v1'),  , s'),  , ! cnstrs1) else addConstraint (cnstrs2,  , ref (eqn (g,  , eClo us2,  , eClo us1))) else addConstraint (cnstrs1,  , ref (eqn (g,  , eClo us1,  , eClo us2))) else if isPatSub (s1) then let let  inlet  in in (* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
(* invertExpW (Us2, s1, ref NONE) *)
instantiateEVar (r1,  , u2',  , ! cnstrs1) else if isPatSub (s2) then let let  inlet  in in (* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
(* invertExpW (Us1, s2, ref NONE) *)
instantiateEVar (r2,  , u1',  , ! cnstrs2) else let let  in in addConstraint (cnstrs1,  , cnstr) unifyExpW(g,  , us1 as (eVar (r,  , gX,  , v,  , cnstrs),  , s),  , us2 as (u2,  , s2)) if isPatSub (s) then let let  inlet  in in (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
(* invertExpW (Us2, s, r) *)
instantiateEVar (r,  , u2',  , ! cnstrs) else addConstraint (cnstrs,  , ref (eqn (g,  , eClo us1,  , eClo us2))) unifyExpW(g,  , us1 as (u1,  , s1),  , us2 as (eVar (r,  , gX,  , v,  , cnstrs),  , s)) if isPatSub (s) then let let  inlet  in in (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
(* invertExpW (Us1, s, r) *)
instantiateEVar (r,  , u1',  , ! cnstrs) else addConstraint (cnstrs,  , ref (eqn (g,  , eClo us1,  , eClo us2))) unifyExpW(g,  , us1,  , us2) raise (unify ("Expression clash"))(* covers most remaining cases *)
(* the cases for EClo or Redex should not occur because of whnf invariant *)
(* unifyExp (G, (U1, s1), (U2, s2)) = ()
       as in unifyExpW, except that arguments may not be in whnf
    *)
 unifyExp(g,  , us1 as (e1,  , s1),  , us2 as (e2,  , s2)) unifyExpW (g,  , whnf us1,  , whnf us2) unifyDefDefW(g,  , us1 as (root (def (d1),  , s1),  , s1),  , us2 as (root (def (d2),  , s2),  , s2)) let let  inlet  inlet  in(* conservative *)
 in match compare (h1,  , h2) with eQUAL -> unifyExpW (g,  , expandDef (us1),  , expandDef (us2)) lESS -> unifyExpW (g,  , us1,  , expandDef (us2)) gREATER -> unifyExpW (g,  , expandDef (us1),  , us2)(* unifySpine (G, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- S1 : V1 > W1
       and  G |- s2 : G2   G2 |- S2 : V2 > W2
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  G |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. G |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
 unifySpine(g,  , (nil,  , _),  , (nil,  , _)) () unifySpine(g,  , (sClo (s1,  , s1'),  , s1),  , ss) unifySpine (g,  , (s1,  , comp (s1',  , s1)),  , ss) unifySpine(g,  , ss,  , (sClo (s2,  , s2'),  , s2)) unifySpine (g,  , ss,  , (s2,  , comp (s2',  , s2))) unifySpine(g,  , (app (u1,  , s1),  , s1),  , (app (u2,  , s2),  , s2)) (unifyExp (g,  , (u1,  , s1),  , (u2,  , s2)); unifySpine (g,  , (s1,  , s1),  , (s2,  , s2)))(* Nil/App or App/Nil cannot occur by typing invariants *)
 unifyDec(g,  , (dec (_,  , v1),  , s1),  , (dec (_,  , v2),  , s2)) unifyExp (g,  , (v1,  , s1),  , (v2,  , s2))(* unifySub (G, s1, s2) = ()

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then unifySub (G, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  unifySub is used only to unify the instantiation of SOME variables
    *)
(* conjecture: G == Null at all times *)
(* Thu Dec  6 21:01:09 2001 -fp *)
 unifySub(g,  , shift (n1),  , shift (n2)) () unifySub(g,  , shift (n),  , s2 as dot _) unifySub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , s2) unifySub(g,  , s1 as dot _,  , shift (m)) unifySub (g,  , s1,  , dot (idx (m + 1),  , shift (m + 1))) unifySub(g,  , dot (ft1,  , s1),  , dot (ft2,  , s2)) ((match (ft1,  , ft2) with (idx (n1),  , idx (n2)) -> if n1 <> n2 then raise (error "SOME variables mismatch") else () (exp (u1),  , exp (u2)) -> unifyExp (g,  , (u1,  , id),  , (u2,  , id)) (exp (u1),  , idx (n2)) -> unifyExp (g,  , (u1,  , id),  , (root (bVar (n2),  , nil),  , id)) (idx (n1),  , exp (u2)) -> unifyExp (g,  , (root (bVar (n1),  , nil),  , id),  , (u2,  , id))); (*         | (Undef, Undef) =>
           | _ => false *)
(* not possible because of invariant? -cs *)
unifySub (g,  , s1,  , s2))(* substitutions s1 and s2 were redundant here --- removed *)
(* Sat Dec  8 11:47:12 2001 -fp !!! *)
 unifyBlock(g,  , lVar (ref (sOME (b1)),  , s,  , _),  , b2) unifyBlock (g,  , blockSub (b1,  , s),  , b2) unifyBlock(g,  , b1,  , lVar (ref (sOME (b2)),  , s,  , _)) unifyBlock (g,  , b1,  , blockSub (b2,  , s)) unifyBlock(g,  , b1,  , b2) unifyBlockW (g,  , b1,  , b2) unifyBlockW(g,  , lVar (r1,  , s1 as shift (k1),  , (l1,  , t1)),  , lVar (r2,  , s2 as shift (k2),  , (l2,  , t2))) if l1 <> l2 then raise (unify "Label clash") else if r1 = r2 then () else (unifySub (g,  , comp (t1,  , s1),  , comp (t2,  , s2)); (* Sat Dec  7 22:04:31 2002 -fp *)
(* was: unifySub (G, t1, t2)  Jul 22 2010 *)
if k1 < k2 then instantiateLVar (r1,  , lVar (r2,  , shift (k2 - k1),  , (l2,  , t2))) else instantiateLVar (r2,  , lVar (r1,  , shift (k1 - k2),  , (l1,  , t1)))) unifyBlockW(g,  , lVar (r1,  , s1,  , (l1,  , t1)),  , b2) instantiateLVar (r1,  , blockSub (b2,  , invert s1)) unifyBlockW(g,  , b1,  , lVar (r2,  , s2,  , (l2,  , t2))) instantiateLVar (r2,  , blockSub (b1,  , invert s2)) unifyBlockW(g,  , bidx (n1),  , (bidx (n2))) if n1 <> n2 then raise (unify "Block index clash") else ()(*
      | unifyBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | unifyBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
let rec unify1W(g,  , us1,  , us2) (unifyExpW (g,  , us1,  , us2); awakeCnstr (nextCnstr ())) unify1(g,  , us1,  , us2) (unifyExp (g,  , us1,  , us2); awakeCnstr (nextCnstr ())) awakeCnstr(nONE) () awakeCnstr(sOME (ref solved)) awakeCnstr (nextCnstr ()) awakeCnstr(sOME (cnstr as ref (eqn (g,  , u1,  , u2)))) (solveConstraint cnstr; unify1 (g,  , (u1,  , id),  , (u2,  , id))) awakeCnstr(sOME (ref (fgnCnstr csfc))) if (apply csfc ()) then () else raise (unify "Foreign constraint violated")let rec unifyW(g,  , us1,  , us2) (resetAwakenCnstrs (); unify1W (g,  , us1,  , us2))let rec unify(g,  , us1,  , us2) (resetAwakenCnstrs (); unify1 (g,  , us1,  , us2))type UnifTraillet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet  inlet rec invertible(g,  , us,  , ss,  , rOccur) try  with let  inlet rec unifiable(g,  , us1,  , us2) try  with let rec unifiable'(g,  , us1,  , us2) try  with end