open Basis

(* Matching *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module type MATCH = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (* matching *)
  exception Match of string

  val match_ : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val matchW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val matchBlock : IntSyn.dctx * IntSyn.block * IntSyn.block -> unit

  (* raises Unify *)
  val matchSub : IntSyn.dctx * IntSyn.sub * IntSyn.sub -> unit

  (* raises Unify *)
  (* instance (G, Us,Us') will instantiate an effect 
     checks if Us' is an instance of Us *)
  val instance : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* instance' (G, Us,Us') is like instance, but returns NONE for_sml
     success and SOME(msg) for_sml failure *)
  val instance' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option
end

(* signature MATCH *)
(* Matching *)

(* Unification modified to Matching *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* Modified: Roberto Virga, Brigitte Pientka *)

module Match (Whnf : Whnf.WHNF) (Unify : Unify.UNIFY) (Trail : Trail.TRAIL) :
  MATCH = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Match of string
  exception NotInvertible

  open IntSyn

  let delayExp = Unify.delay
  (* weakenSub (G1, s, ss) = w'

       Invariant:
       If    G |- s : G1       (* s patsub *)
       and   G2 |- ss : G      (* ss strsub *)
       then  G1 |- w' : G1'    (* w' weaksub *)

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
    *)

  let rec weakenSub = function
    | G, Shift n, ss ->
        if n < ctxLength G then
          weakenSub (G, Dot (Idx (n + 1), Shift (n + 1)), ss)
        else id
    | G, Dot (Idx n, s'), ss -> (
        match bvarSub (n, ss) with
        | Undef -> comp (weakenSub (G, s', ss), shift)
        | Idx _ -> dot1 (weakenSub (G, s', ss)))
    | G, Dot (Undef, s'), ss -> comp (weakenSub (G, s', ss), shift)
  (* prune (G, (U, s), ss, rOccur) = U[s][ss]

       !!! looks wrong to me -kw
       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'

       !!! i would say
       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Match if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)

  let rec pruneExp (G, Us, ss, rOccur) = pruneExpW (G, Whnf.whnf Us, ss, rOccur)

  and pruneExpW = function
    | G, (U, s), _, _ -> U
    | G, (Pi ((D, P), V), s), ss, rOccur ->
        Pi
          ( (pruneDec (G, (D, s), ss, rOccur), P),
            pruneExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur) )
    | G, (Lam (D, V), s), ss, rOccur ->
        Lam
          ( pruneDec (G, (D, s), ss, rOccur),
            pruneExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur) )
    | G, (Root (H, S), s (* = id *)), ss, rOccur ->
        Root (pruneHead (G, H, ss, rOccur), pruneSpine (G, (S, s), ss, rOccur))
    | G, (X, s), ss, rOccur -> (
        if rOccur = r then raise (Match "Variable occurrence")
        else if Whnf.isPatSub s then
          let w = weakenSub (G, s, ss) in
          if Whnf.isId w then EClo (X, comp (s, ss))
          else
            raise (Match "Invertible Substitution does not necessarily exist\n")
          (* let
                     val wi = Whnf.invert w
                     (* val V' = EClo (V, wi) *)
                     val V' = pruneExp (GX, (V, id), wi, rOccur)
                     (* val GY = Whnf.strengthen (wi, GX) *)
                     val GY = pruneCtx (wi, GX, rOccur)
                     (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
                     (* could optimize by checking for_sml identity subst *)
                     val Y = newEVar (GY, V')
                     val Yw = EClo (Y, w)
                     val _ = Unify.instantiateEVar (r, Yw, !cnstrs)
                   in
                     EClo (Yw, comp (s, ss))
                   end*)
        else (* s not patsub *)
          (* -bp not sure what to do in the non-pattern case *)
          try EClo (X, Unify.invertSub (G, s, ss, rOccur))
          with NotInvertible ->
            (* val GY = Whnf.strengthen (ss, G) *)
            (* shortcuts possible by invariants on G? *)
            (* prune or invert??? *)
            (* val V' = EClo (V, comp (s, ss)) *)
            (* prune or invert??? *)
            let GY = pruneCtx (ss, G, rOccur) in
            let V' = pruneExp (G, (V, s), ss, rOccur) in
            let Y = newEVar (GY, V') in
            let _ =
              Unify.addConstraint
                (cnstrs, ref (Eqn (G, EClo (X, s), EClo (Y, Whnf.invert ss))))
            in
            Y)
    | G, (FgnExp csfe, s), ss, rOccur ->
        FgnExpStd.Map.apply csfe (fun U -> pruneExp (G, (U, s), ss, rOccur))
    | G, (X, s), ss, rOccur -> raise (Match "Left-over AVar")

  and pruneDec = function
    | G, (Dec (name, V), s), ss, rOccur ->
        Dec (name, pruneExp (G, (V, s), ss, rOccur))
    | G, (NDec x, _), _, _ -> NDec x

  and pruneSpine = function
    | G, (Nil, s), ss, rOccur -> Nil
    | G, (App (U, S), s), ss, rOccur ->
        App
          (pruneExp (G, (U, s), ss, rOccur), pruneSpine (G, (S, s), ss, rOccur))
    | G, (SClo (S, s'), s), ss, rOccur ->
        pruneSpine (G, (S, comp (s', s)), ss, rOccur)

  and pruneHead = function
    | G, BVar k, ss, rOccur -> (
        match bvarSub (k, ss) with
        | Undef -> raise (Match "Parameter dependency")
        | Idx k' -> BVar k')
    | G, H, ss, rOccur -> H
    | G, Proj (B, i), ss, rOccur -> (
        match blockSub (B, ss) with Bidx k' -> Proj (Bidx k', i))
    | G, H, ss, rOccur ->
        pruneSub (G, t, id, rOccur);
        H
    | G, H, ss, rOccur -> H
    | G, H, ss, rOccur -> H
    | G, FVar (x, V, s'), ss, rOccur ->
        pruneExp (G, (V, id), id, rOccur);
        (* why G here? -fp !!! *)
        FVar (x, V, comp (s', ss))
    | G, H, ss, rOccur -> H

  and pruneSub = function
    | G, s, ss, rOccur ->
        if n < ctxLength G then
          pruneSub (G, Dot (Idx (n + 1), Shift (n + 1)), ss, rOccur)
        else comp (s, ss)
    | G, Dot (Idx n, s'), ss, rOccur -> (
        match bvarSub (n, ss) with
        | Undef -> raise (Match "Not prunable")
        | Ft -> Dot (Ft, pruneSub (G, s', ss, rOccur)))
    | G, Dot (Exp U, s'), ss, rOccur ->
        Dot
          (Exp (pruneExp (G, (U, id), ss, rOccur)), pruneSub (G, s', ss, rOccur))

  and pruneCtx = function
    | Shift n, Null, rOccur -> Null
    | Dot (Idx k, t), Decl (G, D), rOccur ->
        let t' = comp (t, invShift) in
        let D' = pruneDec (G, (D, id), t', rOccur) in
        Decl (pruneCtx (t', G, rOccur), D')
    | Dot (Undef, t), Decl (G, d), rOccur -> pruneCtx (t, G, rOccur)
    | Shift n, G, rOccur ->
        pruneCtx (Dot (Idx (n + 1), Shift (n + 1)), G, rOccur)
  (* matchExpW (G, (U1, s1), (U2, s2)) = ()

       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf
       and  G |- V1 [s1] = V2 [s2]  : L    (for_sml some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, U1, s2, U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is effect, () returned
            else exception Match is raised
       Other effects: EVars may be lowered
                      constraints may be added for_sml non-patterns
    *)

  let rec matchExpW = function
    | G, Us1, Us2 -> (
        match FgnExpStd.UnifyWith.apply csfe1 (G, EClo Us2) with
        | Succeed residualL ->
            let rec execResidual = function
              | Assign (G, EVar (r, _, _, cnstrs), W, ss) ->
                  let W' = pruneExp (G, (W, id), ss, r) in
                  Unify.instantiateEVar (r, W', !cnstrs)
              | Delay (U, cnstr) -> delayExp ((U, id), cnstr)
            in
            List.app execResidual residualL
        | Fail -> raise (Match "Foreign Expression Mismatch"))
    | G, Us1, Us2 -> (
        match FgnExpStd.UnifyWith.apply csfe2 (G, EClo Us1) with
        | Succeed opL ->
            let rec execOp = function
              | Assign (G, EVar (r, _, _, cnstrs), W, ss) ->
                  let W' = pruneExp (G, (W, id), ss, r) in
                  Unify.instantiateEVar (r, W', !cnstrs)
              | Delay (U, cnstr) -> delayExp ((U, id), cnstr)
            in
            List.app execOp opL
        | Fail -> raise (Match "Foreign Expression Mismatch"))
    | G, (Uni L1, _), (Uni L2, _) -> ()
    | G, Us1, Us2 -> (
        match (H1, H2) with
        | BVar k1, BVar k2 ->
            if k1 = k2 then matchSpine (G, (S1, s1), (S2, s2))
            else raise (Match "Bound variable clash")
        | Const c1, Const c2 ->
            if c1 = c2 then matchSpine (G, (S1, s1), (S2, s2))
            else raise (Match "Constant clash")
        | Proj (b1, i1), Proj (b2, i2) ->
            if i1 = i2 then (
              matchBlock (G, b1, b2);
              matchSpine (G, (S1, s1), (S2, s2)))
            else raise (Match "Global parameter clash")
        | Skonst c1, Skonst c2 ->
            if c1 = c2 then matchSpine (G, (S1, s1), (S2, s2))
            else raise (Match "Skolem constant clash")
        | FVar (n1, _, _), FVar (n2, _, _) ->
            if n1 = n2 then matchSpine (G, (S1, s1), (S2, s2))
            else raise (Match "Free variable clash")
        | Def d1, Def d2 ->
            if d1 = d2 then (* because of strict *)
              matchSpine (G, (S1, s1), (S2, s2))
            else
              (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
              matchDefDefW (G, Us1, Us2)
              (* four new cases for_sml defined constants *)
        | Def d1, Const c2 -> (
            match defAncestor d1 with
            | Anc (_, _, None) ->
                (* conservative *)
                matchExpW (G, Whnf.expandDef Us1, Us2)
            | Anc (_, _, Some c1) ->
                if c1 = c2 then matchExpW (G, Whnf.expandDef Us1, Us2)
                else raise (Match "Constant clash"))
        | Const c1, Def d2 -> (
            match defAncestor d2 with
            | Anc (_, _, None) ->
                (* conservative *)
                matchExpW (G, Us1, Whnf.expandDef Us2)
            | Anc (_, _, Some c2) ->
                if c1 = c2 then matchExpW (G, Us1, Whnf.expandDef Us2)
                else raise (Match "Constant clash"))
        | Def d1, BVar k2 ->
            raise (Match "Head mismatch") (* due to strictness! *)
        | BVar k1, Def d2 ->
            raise (Match "Head mismatch") (* due to strictness! *)
        (* next two cases for_sml def/fgn, fgn/def *)
        | Def d1, _ -> matchExpW (G, Whnf.expandDef Us1, Us2)
        | _, Def d2 -> matchExpW (G, Us1, Whnf.expandDef Us2)
        | ( FgnConst (cs1, ConDec (n1, _, _, _, _, _)),
            FgnConst (cs2, ConDec (n2, _, _, _, _, _)) ) ->
            (* we require unique string representation of external constants *)
            if cs1 = cs2 && n1 = n2 then ()
            else raise (Match "Foreign Constant clash")
        | ( FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)),
            FgnConst (cs2, ConDef (n2, _, _, V, W2, _, _)) ) ->
            if cs1 = cs2 && n1 = n2 then () else matchExp (G, (W1, s1), (W2, s2))
        | FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _ ->
            matchExp (G, (W1, s1), Us2)
        | _, FgnConst (_, ConDef (_, _, _, W2, _, _, _)) ->
            matchExp (G, Us1, (W2, s2))
        | _ -> raise (Match "Head mismatch"))
    | G, (Pi ((D1, _), U1), s1), (Pi ((D2, _), U2), s2) ->
        matchDec (G, (D1, s1), (D2, s2));
        matchExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), (U2, dot1 s2))
    | G, Us1, Us2 -> matchExpW (G, Us1, Whnf.expandDef Us2)
    | G, Us1, Us2 -> matchExpW (G, Whnf.expandDef Us1, Us2)
    | G, (Lam (D1, U1), s1), (Lam (D2, U2), s2) ->
        matchExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), (U2, dot1 s2))
    | G, (Lam (D1, U1), s1), (U2, s2) ->
        matchExp
          ( Decl (G, decSub (D1, s1)),
            (U1, dot1 s1),
            (Redex (EClo (U2, shift), App (Root (BVar 1, Nil), Nil)), dot1 s2)
          )
    | G, (U1, s1), (Lam (D2, U2), s2) ->
        matchExp
          ( Decl (G, decSub (D2, s2)),
            (Redex (EClo (U1, shift), App (Root (BVar 1, Nil), Nil)), dot1 s1),
            (U2, dot1 s2) )
    | G, Us1, Us2 ->
        if Whnf.isPatSub s then
          let ss = Whnf.invert s in
          let U2' = pruneExp (G, Us2, ss, r) in
          (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
          (* invertExpW (Us2, s, r) *)
          Unify.instantiateEVar (r, U2', !cnstrs)
        else Unify.addConstraint (cnstrs, ref (Eqn (G, EClo Us1, EClo Us2)))
    | G, Us1, Us2 -> raise (Match "Expression clash")

  and matchExp (G, Us1, Us2) = matchExpW (G, Whnf.whnf Us1, Whnf.whnf Us2)

  and matchDefDefW (G, Us1, Us2) =
    (*  matchExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
    (* conservative *)
    let (Anc (_, h1, c1Opt)) = defAncestor d1 in
    let (Anc (_, h2, c2Opt)) = defAncestor d2 in
    let _ =
      match (c1Opt, c2Opt) with
      | Some c1, Some c2 ->
          if c1 <> c2 then raise (Match "Irreconcilable defined constant clash")
          else ()
      | _ -> ()
    in
    match Int.compare (h1, h2) with
    | Eq -> matchExpW (G, Whnf.expandDef Us1, Whnf.expandDef Us2)
    | Lt -> matchExpW (G, Us1, Whnf.expandDef Us2)
    | Gt -> matchExpW (G, Whnf.expandDef Us1, Us2)

  and matchSpine = function
    | G, (Nil, _), (Nil, _) -> ()
    | G, (SClo (S1, s1'), s1), Ss -> matchSpine (G, (S1, comp (s1', s1)), Ss)
    | G, Ss, (SClo (S2, s2'), s2) -> matchSpine (G, Ss, (S2, comp (s2', s2)))
    | G, (App (U1, S1), s1), (App (U2, S2), s2) ->
        matchExp (G, (U1, s1), (U2, s2));
        matchSpine (G, (S1, s1), (S2, s2))

  and matchDec (G, (Dec (_, V1), s1), (Dec (_, V2), s2)) =
    matchExp (G, (V1, s1), (V2, s2))

  and matchSub = function
    | G, Shift n1, Shift n2 -> ()
    | G, Shift n, s2 -> matchSub (G, Dot (Idx (n + 1), Shift (n + 1)), s2)
    | G, s1, Shift m -> matchSub (G, s1, Dot (Idx (m + 1), Shift (m + 1)))
    | G, Dot (Ft1, s1), Dot (Ft2, s2) ->
        (match (Ft1, Ft2) with
        | Idx n1, Idx n2 ->
            if n1 <> n2 then raise (Error "SOME variables mismatch") else ()
        | Exp U1, Exp U2 -> matchExp (G, (U1, id), (U2, id))
        | Exp U1, Idx n2 -> matchExp (G, (U1, id), (Root (BVar n2, Nil), id))
        | Idx n1, Exp U2 -> matchExp (G, (Root (BVar n1, Nil), id), (U2, id)));
        (*         | (Undef, Undef) =>
           | _ => false *)
        (* not possible because of invariant? -cs *)
        matchSub (G, s1, s2)

  and matchBlock = function
    | G, LVar ({ contents = Some B1 }, s, _), B2 ->
        matchBlock (G, blockSub (B1, s), B2)
    | G, B1, LVar ({ contents = Some B2 }, s, _) ->
        matchBlock (G, B1, blockSub (B2, s))
    | G, B1, B2 -> matchBlockW (G, B1, B2)

  and matchBlockW = function
    | G, LVar (r1, Shift k1, (l1, t1)), LVar (r2, Shift k2, (l2, t2)) ->
        if l1 <> l2 then raise (Match "Label clash")
        else if r1 = r2 then ()
        else (
          matchSub (G, t1, t2);
          (* Sat Dec  7 22:04:31 2002 -fp *)
          (* invariant? always k1 = k2? *)
          (* prune t2? Sat Dec  7 22:09:53 2002 *)
          if k1 <> k2 then raise Bind else ();
          (*
              if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
                else Unify.instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
              *)
          (* hack! *)
          let ss = Whnf.invert (Shift k1) in
          let t2' = pruneSub (G, t2, ss, ref None) in
          Unify.instantiateLVar (r1, LVar (r2, Shift 0, (l2, t2')))
          (* 0 = k2-k1 *))
    | G, LVar (r1, s1, (l1, t1)), B2 ->
        r1 := Some (blockSub (B2, Whnf.invert s1));
        ()
    | G, B1, LVar (r2, s2, (l2, t2)) ->
        r2 := Some (blockSub (B1, Whnf.invert s2));
        ()
    | G, Bidx n1, Bidx n2 ->
        if n1 <> n2 then raise (Match "Block index clash") else ()
  (*
      | matchBlock (LVar (r1, _, _), Bidx _) = instantiate (r1, B)
      | matchBlock (Bidx _, LVar (r2, _, _)) =

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs

*)

  let rec match1W (G, Us1, Us2) =
    matchExpW (G, Us1, Us2);
    awakeCnstr (Unify.nextCnstr ())

  and match1 (G, Us1, Us2) =
    matchExp (G, Us1, Us2);
    awakeCnstr (Unify.nextCnstr ())

  and awakeCnstr = function
    | None -> ()
    | Some { contents = Solved } -> awakeCnstr (Unify.nextCnstr ())
    | Some cnstr ->
        Unify.solveConstraint cnstr;
        match1 (G, (U1, id), (U2, id))
    | Some { contents = FgnCnstr csfc } ->
        if FgnCnstrStd.Awake.apply csfc () then ()
        else raise (Match "Foreign constraint violated")

  let rec matchW (G, Us1, Us2) =
    Unify.resetAwakenCnstrs ();
    match1W (G, Us1, Us2)

  let rec match_ (G, Us1, Us2) =
    Unify.resetAwakenCnstrs ();
    match1 (G, Us1, Us2)

  let matchW = matchW
  let match_ = match_
  let matchSub = matchSub
  let matchBlock = matchBlock

  let rec instance (G, Us1, Us2) =
    try
      match_ (G, Us1, Us2);
      true
    with Match msg -> false

  let rec instance' (G, Us1, Us2) =
    try
      match_ (G, Us1, Us2);
      None
    with Match msg -> Some msg
end

(* functor Match *)
