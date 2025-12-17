Match  Whnf WHNF    Unify UNIFY    Trail TRAIL     MATCH  struct (*! structure IntSyn = IntSyn' !*)
exception exception open IntSyn let  in(* weakenSub (G1, s, ss) = w'

       Invariant:
       If    G |- s : G1       (* s patsub *)
       and   G2 |- ss : G      (* ss strsub *)
       then  G1 |- w' : G1'    (* w' weaksub *)

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
    *)
let rec weakenSub(g,  , shift n,  , ss) if n < ctxLength g then weakenSub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , ss) else id weakenSub(g,  , dot (idx n,  , s'),  , ss) (match bvarSub (n,  , ss) with undef -> comp (weakenSub (g,  , s',  , ss),  , shift) idx _ -> dot1 (weakenSub (g,  , s',  , ss))) weakenSub(g,  , dot (undef,  , s'),  , ss) comp (weakenSub (g,  , s',  , ss),  , shift)(* prune (G, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'

       !!! i would say
       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Match if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
let rec pruneExp(g,  , us,  , ss,  , rOccur) pruneExpW (g,  , whnf us,  , ss,  , rOccur) pruneExpW(g,  , (u as uni _,  , s),  , _,  , _) u pruneExpW(g,  , (pi ((d,  , p),  , v),  , s),  , ss,  , rOccur) pi ((pruneDec (g,  , (d,  , s),  , ss,  , rOccur),  , p),  , pruneExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , dot1 ss,  , rOccur)) pruneExpW(g,  , (lam (d,  , v),  , s),  , ss,  , rOccur) lam (pruneDec (g,  , (d,  , s),  , ss,  , rOccur),  , pruneExp (decl (g,  , decSub (d,  , s)),  , (v,  , dot1 s),  , dot1 ss,  , rOccur)) pruneExpW(g,  , (root (h,  , s),  , s, (* = id *)
),  , ss,  , rOccur) root (pruneHead (g,  , h,  , ss,  , rOccur),  , pruneSpine (g,  , (s,  , s),  , ss,  , rOccur)) pruneExpW(g,  , (x as eVar (r,  , gX,  , v,  , cnstrs),  , s),  , ss,  , rOccur) if (rOccur = r) then raise (match "Variable occurrence") else if isPatSub (s) then let let  in in if isId w then eClo (x,  , comp (s,  , ss)) else raise (match "Invertible Substitution does not necessarily exist\n")(* let
                     val wi = Whnf.invert w
                     (* val V' = EClo (V, wi) *)
                     val V' = pruneExp (GX, (V, id), wi, rOccur)
                     (* val GY = Whnf.strengthen (wi, GX) *)
                     val GY = pruneCtx (wi, GX, rOccur)
                     (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
                     (* could optimize by checking for identity subst *)
                     val Y = newEVar (GY, V')
                     val Yw = EClo (Y, w)
                     val _ = Unify.instantiateEVar (r, Yw, !cnstrs)
                   in
                     EClo (Yw, comp (s, ss))
                   end*)
 else (* s not patsub *)
(* -bp not sure what to do in the non-pattern case *)
(try  with ) pruneExpW(g,  , (fgnExp csfe,  , s),  , ss,  , rOccur) apply csfe (fun u -> pruneExp (g,  , (u,  , s),  , ss,  , rOccur)) pruneExpW(g,  , ((x as aVar _),  , s),  , ss,  , rOccur) raise (match "Left-over AVar")(* other cases impossible since (U,s1) whnf *)
 pruneDec(g,  , (dec (name,  , v),  , s),  , ss,  , rOccur) dec (name,  , pruneExp (g,  , (v,  , s),  , ss,  , rOccur)) pruneDec(g,  , (nDec x,  , _),  , _,  , _) nDec x(* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
 pruneSpine(g,  , (nil,  , s),  , ss,  , rOccur) nil pruneSpine(g,  , (app (u,  , s),  , s),  , ss,  , rOccur) app (pruneExp (g,  , (u,  , s),  , ss,  , rOccur),  , pruneSpine (g,  , (s,  , s),  , ss,  , rOccur)) pruneSpine(g,  , (sClo (s,  , s'),  , s),  , ss,  , rOccur) pruneSpine (g,  , (s,  , comp (s',  , s)),  , ss,  , rOccur) pruneHead(g,  , bVar k,  , ss,  , rOccur) (match (bvarSub (k,  , ss)) with undef -> raise (match "Parameter dependency") idx k' -> bVar k') pruneHead(g,  , h as const _,  , ss,  , rOccur) h pruneHead(g,  , proj (b as bidx k,  , i),  , ss,  , rOccur) (match blockSub (b,  , ss) with bidx (k') -> proj (bidx (k'),  , i)) pruneHead(g,  , h as proj (lVar (r,  , sk,  , (l,  , t)),  , i),  , ss,  , rOccur) (pruneSub (g,  , t,  , id,  , rOccur); h) pruneHead(g,  , h as skonst _,  , ss,  , rOccur) h pruneHead(g,  , h as def _,  , ss,  , rOccur) h pruneHead(g,  , fVar (x,  , v,  , s'),  , ss,  , rOccur) (pruneExp (g,  , (v,  , id),  , id,  , rOccur); (* why G here? -fp !!! *)
fVar (x,  , v,  , comp (s',  , ss))) pruneHead(g,  , h as fgnConst _,  , ss,  , rOccur) h(* pruneSub never allows pruning OUTDATED *)
(* in the presence of block variables, this invariant
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
 pruneSub(g,  , s as shift (n),  , ss,  , rOccur) if n < ctxLength (g) then pruneSub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , ss,  , rOccur) else comp (s,  , ss) pruneSub(g,  , dot (idx (n),  , s'),  , ss,  , rOccur) (match bvarSub (n,  , ss) with undef -> raise (match "Not prunable") ft -> dot (ft,  , pruneSub (g,  , s',  , ss,  , rOccur))) pruneSub(g,  , dot (exp (u),  , s'),  , ss,  , rOccur) dot (exp (pruneExp (g,  , (u,  , id),  , ss,  , rOccur)),  , pruneSub (g,  , s',  , ss,  , rOccur))(* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
(* By invariant, all EVars X[s] are such that s is defined everywhere *)
(* Pruning establishes and maintains this invariant *)
 pruneCtx(shift n,  , null,  , rOccur) null pruneCtx(dot (idx k,  , t),  , decl (g,  , d),  , rOccur) let let  inlet  in in decl (pruneCtx (t',  , g,  , rOccur),  , d') pruneCtx(dot (undef,  , t),  , decl (g,  , d),  , rOccur) pruneCtx (t,  , g,  , rOccur) pruneCtx(shift n,  , g,  , rOccur) pruneCtx (dot (idx (n + 1),  , shift (n + 1)),  , g,  , rOccur)(* matchExpW (G, (U1, s1), (U2, s2)) = ()

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
            else exception Match is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
let rec matchExpW(g,  , us1 as (fgnExp csfe1,  , _),  , us2) (match (apply csfe1 (g,  , eClo us2)) with (succeed residualL) -> let let rec execResidual(assign (g,  , eVar (r,  , _,  , _,  , cnstrs),  , w,  , ss)) let let  in in instantiateEVar (r,  , w',  , ! cnstrs) execResidual(delay (u,  , cnstr)) delayExp ((u,  , id),  , cnstr) in app execResidual residualL fail -> raise (match "Foreign Expression Mismatch")) matchExpW(g,  , us1,  , us2 as (fgnExp csfe2,  , _)) (match (apply csfe2 (g,  , eClo us1)) with (succeed opL) -> let let rec execOp(assign (g,  , eVar (r,  , _,  , _,  , cnstrs),  , w,  , ss)) let let  in in instantiateEVar (r,  , w',  , ! cnstrs) execOp(delay (u,  , cnstr)) delayExp ((u,  , id),  , cnstr) in app execOp opL fail -> raise (match "Foreign Expression Mismatch")) matchExpW(g,  , (uni (l1),  , _),  , (uni (l2),  , _)) () matchExpW(g,  , us1 as (root (h1,  , s1),  , s1),  , us2 as (root (h2,  , s2),  , s2)) (match (h1,  , h2) with (bVar (k1),  , bVar (k2)) -> if (k1 = k2) then matchSpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (match "Bound variable clash") (const (c1),  , const (c2)) -> if (c1 = c2) then matchSpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (match "Constant clash") (proj (b1,  , i1),  , proj (b2,  , i2)) -> if (i1 = i2) then (matchBlock (g,  , b1,  , b2); matchSpine (g,  , (s1,  , s1),  , (s2,  , s2))) else raise (match "Global parameter clash") (skonst (c1),  , skonst (c2)) -> if (c1 = c2) then matchSpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (match "Skolem constant clash") (fVar (n1,  , _,  , _),  , fVar (n2,  , _,  , _)) -> if (n1 = n2) then matchSpine (g,  , (s1,  , s1),  , (s2,  , s2)) else raise (match "Free variable clash") (def (d1),  , def (d2)) -> if (d1 = d2) then (* because of strict *)
matchSpine (g,  , (s1,  , s1),  , (s2,  , s2)) else (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
matchDefDefW (g,  , us1,  , us2)(* four new cases for defined constants *)
 (def (d1),  , const (c2)) -> (match defAncestor d1 with anc (_,  , _,  , nONE) -> (* conservative *)
matchExpW (g,  , expandDef us1,  , us2) anc (_,  , _,  , sOME (c1)) -> if (c1 = c2) then matchExpW (g,  , expandDef us1,  , us2) else raise (match "Constant clash")) (const (c1),  , def (d2)) -> (match defAncestor d2 with anc (_,  , _,  , nONE) -> (* conservative *)
matchExpW (g,  , us1,  , expandDef us2) anc (_,  , _,  , sOME (c2)) -> if (c1 = c2) then matchExpW (g,  , us1,  , expandDef us2) else raise (match "Constant clash")) (def (d1),  , bVar (k2)) -> raise (match "Head mismatch")(* due to strictness! *)
 (bVar (k1),  , def (d2)) -> raise (match "Head mismatch")(* due to strictness! *)
(* next two cases for def/fgn, fgn/def *)
 (def (d1),  , _) -> matchExpW (g,  , expandDef us1,  , us2) (_,  , def (d2)) -> matchExpW (g,  , us1,  , expandDef us2) (fgnConst (cs1,  , conDec (n1,  , _,  , _,  , _,  , _,  , _)),  , fgnConst (cs2,  , conDec (n2,  , _,  , _,  , _,  , _,  , _))) -> (* we require unique string representation of external constants *)
if (cs1 = cs2) && (n1 = n2) then () else raise (match "Foreign Constant clash") (fgnConst (cs1,  , conDef (n1,  , _,  , _,  , w1,  , _,  , _,  , _)),  , fgnConst (cs2,  , conDef (n2,  , _,  , _,  , v,  , w2,  , _,  , _))) -> if (cs1 = cs2) && (n1 = n2) then () else matchExp (g,  , (w1,  , s1),  , (w2,  , s2)) (fgnConst (_,  , conDef (_,  , _,  , _,  , w1,  , _,  , _,  , _)),  , _) -> matchExp (g,  , (w1,  , s1),  , us2) (_,  , fgnConst (_,  , conDef (_,  , _,  , _,  , w2,  , _,  , _,  , _))) -> matchExp (g,  , us1,  , (w2,  , s2)) _ -> raise (match "Head mismatch")) matchExpW(g,  , (pi ((d1,  , _),  , u1),  , s1),  , (pi ((d2,  , _),  , u2),  , s2)) (matchDec (g,  , (d1,  , s1),  , (d2,  , s2)); matchExp (decl (g,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , (u2,  , dot1 s2))) matchExpW(g,  , us1 as (pi (_,  , _),  , _),  , us2 as (root (def _,  , _),  , _)) matchExpW (g,  , us1,  , expandDef (us2)) matchExpW(g,  , us1 as (root (def _,  , _),  , _),  , us2 as (pi (_,  , _),  , _)) matchExpW (g,  , expandDef (us1),  , us2) matchExpW(g,  , (lam (d1,  , u1),  , s1),  , (lam (d2,  , u2),  , s2)) matchExp (decl (g,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , (u2,  , dot1 s2)) matchExpW(g,  , (lam (d1,  , u1),  , s1),  , (u2,  , s2)) matchExp (decl (g,  , decSub (d1,  , s1)),  , (u1,  , dot1 s1),  , (redex (eClo (u2,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , dot1 s2)) matchExpW(g,  , (u1,  , s1),  , (lam (d2,  , u2),  , s2)) matchExp (decl (g,  , decSub (d2,  , s2)),  , (redex (eClo (u1,  , shift),  , app (root (bVar (1),  , nil),  , nil)),  , dot1 s1),  , (u2,  , dot1 s2)) matchExpW(g,  , us1 as (eVar (r,  , gX,  , v,  , cnstrs),  , s),  , us2 as (u2,  , s2)) if isPatSub (s) then let let  inlet  in in (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
(* invertExpW (Us2, s, r) *)
instantiateEVar (r,  , u2',  , ! cnstrs) else addConstraint (cnstrs,  , ref (eqn (g,  , eClo us1,  , eClo us2))) matchExpW(g,  , us1,  , us2) raise (match ("Expression clash"))(* covers most remaining cases *)
(* the cases for EClo or Redex should not occur because of whnf invariant *)
(* matchExp (G, (U1, s1), (U2, s2)) = ()
       as in matchExpW, except that arguments may not be in whnf
    *)
 matchExp(g,  , us1 as (e1,  , s1),  , us2 as (e2,  , s2)) matchExpW (g,  , whnf us1,  , whnf us2) matchDefDefW(g,  , us1 as (root (def (d1),  , s1),  , s1),  , us2 as (root (def (d2),  , s2),  , s2)) let let  inlet  inlet  in(* conservative *)
 in match compare (h1,  , h2) with eQUAL -> matchExpW (g,  , expandDef (us1),  , expandDef (us2)) lESS -> matchExpW (g,  , us1,  , expandDef (us2)) gREATER -> matchExpW (g,  , expandDef (us1),  , us2)(* matchSpine (G, (S1, s1), (S2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- S1 : V1 > W1
       and  G |- s2 : G2   G2 |- S2 : V2 > W2
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  G |- W1 [s1] = W2 [s2]
       then if   there is an instantiation I :
                 s.t. G |- S1 [s1] <I> == S2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
 matchSpine(g,  , (nil,  , _),  , (nil,  , _)) () matchSpine(g,  , (sClo (s1,  , s1'),  , s1),  , ss) matchSpine (g,  , (s1,  , comp (s1',  , s1)),  , ss) matchSpine(g,  , ss,  , (sClo (s2,  , s2'),  , s2)) matchSpine (g,  , ss,  , (s2,  , comp (s2',  , s2))) matchSpine(g,  , (app (u1,  , s1),  , s1),  , (app (u2,  , s2),  , s2)) (matchExp (g,  , (u1,  , s1),  , (u2,  , s2)); matchSpine (g,  , (s1,  , s1),  , (s2,  , s2)))(* Nil/App or App/Nil cannot occur by typing invariants *)
 matchDec(g,  , (dec (_,  , v1),  , s1),  , (dec (_,  , v2),  , s2)) matchExp (g,  , (v1,  , s1),  , (v2,  , s2))(* matchSub (G, s1, s2) = ()

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then matchSub (G, s1, s2) terminates with ()
            iff there exists an instantiation I, such that
            s1 [I] = s2 [I]

       Remark:  matchSub is used only to match the instantiation of SOME variables
    *)
(* conjecture: G == Null at all times *)
(* Thu Dec  6 21:01:09 2001 -fp *)
 matchSub(g,  , shift (n1),  , shift (n2)) () matchSub(g,  , shift (n),  , s2 as dot _) matchSub (g,  , dot (idx (n + 1),  , shift (n + 1)),  , s2) matchSub(g,  , s1 as dot _,  , shift (m)) matchSub (g,  , s1,  , dot (idx (m + 1),  , shift (m + 1))) matchSub(g,  , dot (ft1,  , s1),  , dot (ft2,  , s2)) ((match (ft1,  , ft2) with (idx (n1),  , idx (n2)) -> if n1 <> n2 then raise (error "SOME variables mismatch") else () (exp (u1),  , exp (u2)) -> matchExp (g,  , (u1,  , id),  , (u2,  , id)) (exp (u1),  , idx (n2)) -> matchExp (g,  , (u1,  , id),  , (root (bVar (n2),  , nil),  , id)) (idx (n1),  , exp (u2)) -> matchExp (g,  , (root (bVar (n1),  , nil),  , id),  , (u2,  , id))); (*         | (Undef, Undef) =>
           | _ => false *)
(* not possible because of invariant? -cs *)
matchSub (g,  , s1,  , s2))(* substitutions s1 and s2 were redundant here --- removed *)
(* Sat Dec  8 11:47:12 2001 -fp !!! *)
 matchBlock(g,  , lVar (ref (sOME (b1)),  , s,  , _),  , b2) matchBlock (g,  , blockSub (b1,  , s),  , b2) matchBlock(g,  , b1,  , lVar (ref (sOME (b2)),  , s,  , _)) matchBlock (g,  , b1,  , blockSub (b2,  , s)) matchBlock(g,  , b1,  , b2) matchBlockW (g,  , b1,  , b2) matchBlockW(g,  , lVar (r1,  , shift (k1),  , (l1,  , t1)),  , lVar (r2,  , shift (k2),  , (l2,  , t2))) if l1 <> l2 then raise (match "Label clash") else if r1 = r2 then () else (matchSub (g,  , t1,  , t2); (* Sat Dec  7 22:04:31 2002 -fp *)
(* invariant? always k1 = k2? *)
(* prune t2? Sat Dec  7 22:09:53 2002 *)
if k1 <> k2 then raise (bind) else (); (*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *)
let let  inlet  in(* hack! *)
 in instantiateLVar (r1,  , lVar (r2,  , shift (0),  , (l2,  , t2')))(* 0 = k2-k1 *)
) matchBlockW(g,  , lVar (r1,  , s1,  , (l1,  , t1)),  , b2) (r1 := sOME (blockSub (b2,  , invert s1)); ()) matchBlockW(g,  , b1,  , lVar (r2,  , s2,  , (l2,  , t2))) (r2 := sOME (blockSub (b1,  , invert s2)); ()) matchBlockW(g,  , bidx (n1),  , (bidx (n2))) if n1 <> n2 then raise (match "Block index clash") else ()(*
      | matchBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B)
      | matchBlock (B as Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)
let rec match1W(g,  , us1,  , us2) (matchExpW (g,  , us1,  , us2); awakeCnstr (nextCnstr ())) match1(g,  , us1,  , us2) (matchExp (g,  , us1,  , us2); awakeCnstr (nextCnstr ())) awakeCnstr(nONE) () awakeCnstr(sOME (ref solved)) awakeCnstr (nextCnstr ()) awakeCnstr(sOME (cnstr as ref (eqn (g,  , u1,  , u2)))) (solveConstraint cnstr; match1 (g,  , (u1,  , id),  , (u2,  , id))) awakeCnstr(sOME (ref (fgnCnstr csfc))) if (apply csfc ()) then () else raise (match "Foreign constraint violated")let rec matchW(g,  , us1,  , us2) (resetAwakenCnstrs (); match1W (g,  , us1,  , us2))let rec match(g,  , us1,  , us2) (resetAwakenCnstrs (); match1 (g,  , us1,  , us2))let  inlet  inlet  inlet  inlet rec instance(g,  , us1,  , us2) try  with let rec instance'(g,  , us1,  , us2) try  with end