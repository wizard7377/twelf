(* Convertibility Modulo Beta and Eta *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module type CONV = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val convDec : (IntSyn.dec * IntSyn.sub) * (IntSyn.dec * IntSyn.sub) -> bool
  val convSub : IntSyn.sub * IntSyn.sub -> bool
end

(* signature CONV *)
(* Convertibility Modulo Beta and Eta *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module Conv (Whnf : Whnf.WHNF) : CONV = struct
  (*! structure IntSyn = IntSyn' !*)

  open IntSyn
  (* eqUni (L1, L2) = B iff L1 = L2 *)

  let rec eqUni = function
    | Type, Type -> true
    | Kind, Kind -> true
    | _ -> false
  (* convExpW ((U1, s1), (U2, s2)) = B

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1) in whnf
            G |- s2 : G2    G2 |- U2 : V2    (U2,s2) in whnf
            G |- V1[s1] == V2[s2] == V : L
       then B iff G |- U1[s1] == U2[s2] : V

       Effects: EVars may be lowered
    *)

  let rec convExpW = function
    | (Uni L1, _), (Uni L2, _) -> eqUni (L1, L2)
    | Us1, Us2 -> (
        match (H1, H2) with
        | BVar k1, BVar k2 -> k1 = k2 && convSpine ((S1, s1), (S2, s2))
        | Const c1, Const c2 -> c1 = c2 && convSpine ((S1, s1), (S2, s2))
        | Skonst c1, Skonst c2 -> c1 = c2 && convSpine ((S1, s1), (S2, s2))
        | Proj (Bidx v1, i1), Proj (Bidx v2, i2) ->
            v1 = v2 && i1 = i2 && convSpine ((S1, s1), (S2, s2))
        | FVar (n1, _, s1'), FVar (n2, _, s2') ->
            (* s1' = s2' = ^|G| *)
            n1 = n2 && convSpine ((S1, s1), (S2, s2))
        | FgnConst (cs1, cD1), FgnConst (cs2, cD2) ->
            (* they must have the same string representation *)
            cs1 = cs2
            && conDecName cD1 = conDecName cD2
            && convSpine ((S1, s1), (S2, s2))
        | Def d1, Def d2 ->
            (* because of strict *)
            (d1 = d2 && convSpine ((S1, s1), (S2, s2)))
            || convExpW (Whnf.expandDef Us1, Whnf.expandDef Us2)
        | Def d1, _ -> convExpW (Whnf.expandDef Us1, Us2)
        | _, Def d2 -> convExpW (Us1, Whnf.expandDef Us2)
        | _ -> false)
    | (Pi (DP1, V1), s1), (Pi (DP2, V2), s2) ->
        convDecP ((DP1, s1), (DP2, s2)) && convExp ((V1, dot1 s1), (V2, dot1 s2))
    | Us1, Us2 -> convExpW (Us1, Whnf.expandDef Us2)
    | Us1, Us2 -> convExpW (Whnf.expandDef Us1, Us2)
    | (Lam (D1, U1), s1), (Lam (D2, U2), s2) ->
        convExp ((U1, dot1 s1), (U2, dot1 s2))
    | (Lam (D1, U1), s1), (U2, s2) ->
        convExp
          ( (U1, dot1 s1),
            (Redex (EClo (U2, shift), App (Root (BVar 1, Nil), Nil)), dot1 s2)
          )
    | (U1, s1), (Lam (D2, U2), s2) ->
        convExp
          ( (Redex (EClo (U1, shift), App (Root (BVar 1, Nil), Nil)), dot1 s1),
            (U2, dot1 s2) )
    | (FgnExp csfe1, s1), Us2 -> FgnExpStd.EqualTo.apply csfe1 (EClo Us2)
    | Us1, (FgnExp csfe2, s2) -> FgnExpStd.EqualTo.apply csfe2 (EClo Us1)
    | (EVar (r1, _, _, _), s1), (EVar (r2, _, _, _), s2) ->
        r1 = r2 && convSub (s1, s2)
    | _ -> false

  and convExp (Us1, Us2) = convExpW (Whnf.whnf Us1, Whnf.whnf Us2)

  and convSpine = function
    | (Nil, _), (Nil, _) -> true
    | (App (U1, S1), s1), (App (U2, S2), s2) ->
        convExp ((U1, s1), (U2, s2)) && convSpine ((S1, s1), (S2, s2))
    | (SClo (S1, s1'), s1), Ss2 -> convSpine ((S1, comp (s1', s1)), Ss2)
    | Ss1, (SClo (S2, s2'), s2) -> convSpine (Ss1, (S2, comp (s2', s2)))
    | _, _ -> false

  and convSub = function
    | Shift n, Shift m -> true
    | Shift n, s2 -> convSub (Dot (Idx (n + 1), Shift (n + 1)), s2)
    | s1, Shift m -> convSub (s1, Dot (Idx (m + 1), Shift (m + 1)))
    | Dot (Ft1, s1), Dot (Ft2, s2) ->
        (match (Ft1, Ft2) with
          | Idx n1, Idx n2 -> n1 = n2
          | Exp U1, Exp U2 -> convExp ((U1, id), (U2, id))
          | Block (Bidx k1), Block (Bidx k2) ->
              k1 = k2 (* other block cases don't matter -cs 2/18/03 *)
          | Exp U1, Idx n2 -> convExp ((U1, id), (Root (BVar n2, Nil), id))
          | Idx n1, Exp U2 -> convExp ((Root (BVar n1, Nil), id), (U2, id))
          | Undef, Undef -> true
          | _ -> false)
        && convSub (s1, s2)

  and convDec = function
    | (Dec (_, V1), s1), (Dec (_, V2), s2) -> convExp ((V1, s1), (V2, s2))
    | (BDec (_, (c1, s1)), t1), (BDec (_, (c2, s2)), t2) ->
        c1 = c2 && convSub (comp (s1, t1), comp (s2, t2))

  and convDecP (((D1, P1), s1), ((D2, P2), s2)) = convDec ((D1, s1), (D2, s2))

  let conv = convExp
  let convDec = convDec
  let convSub = convSub
  (* local *)
end

(* functor Conv *)
