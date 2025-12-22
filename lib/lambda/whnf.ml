(* Weak Head-Normal Forms *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* Modified: Roberto Virga *)

module Whnf : WHNF = struct
  (*! structure IntSyn = IntSyn' !*)

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

  open IntSyn
  (* exception Undefined *)

  exception Eta
  (* etaContract (U, s, n) = k'

       Invariant:
       if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
       then if   lam V1...lam Vn. U[s] =eta*=> k
            then k' = k
            and  G |- k' : Pi V1...Pi Vn. V [s]
            else Eta is raised
              (even if U[s] might be eta-reducible to some other expressions).
    *)

  (* optimization(?): quick check w/o substitution first *)

  let rec etaContract = function
    | Root (BVar k, S), s, n -> (
        match bvarSub (k, s) with
        | Idx k' ->
            if k' > n then (
              etaContract' (S, s, n);
              k' - n)
            else raise Eta
        | _ -> raise Eta)
    | Lam (D, U), s, n -> etaContract (U, dot1 s, n + 1)
    | EClo (U, s'), s, n -> etaContract (U, comp (s', s), n)
    | EVar ({ contents = Some U }, _, _, _), s, n -> etaContract (U, s, n)
    | AVar { contents = Some U }, s, n -> etaContract (U, s, n)
    | _ -> raise Eta

  and etaContract' = function
    | Nil, s, 0 -> ()
    | App (U, S), s, n ->
        if etaContract (U, s, 0) = n then etaContract' (S, s, n - 1)
        else raise Eta
    | SClo (S, s'), s, n -> etaContract' (S, comp (s', s), n)
    | _ -> raise Eta
  (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)

  let rec dotEta = function
    | Ft, s -> Dot (Ft, s)
    | Ft, s ->
        let Ft' = try Idx (etaContract (U, id, 0)) with Eta -> Ft in
        Dot (Ft', s)
    | Ft, s -> Dot (Ft, s)
  (* appendSpine ((S1, s1), (S2, s2)) = S'

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]
    *)

  let rec appendSpine = function
    | (Nil, s1), Ss2 -> SClo Ss2
    | (App (U1, S1), s1), Ss2 -> App (EClo (U1, s1), appendSpine ((S1, s1), Ss2))
    | (SClo (S1, s1'), s1), Ss2 -> appendSpine ((S1, comp (s1', s1)), Ss2)
  (* whnfRedex ((U, s1), (S, s2)) = (U', s')

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

  let rec whnfRedex = function
    | Us, (SClo (S, s2'), s2) -> whnfRedex (Us, (S, comp (s2', s2)))
    | Us, (Nil, s2) -> Us
    | (Root (H1, S1), s1), (S2, s2) ->
        (Root (H1, appendSpine ((S1, s1), (S2, s2))), id)
    | (Lam (_, U1), s1), (App (U2, S), s2) ->
        whnfRedex (whnf (U1, dotEta (frontSub (Exp U2, s2), s1)), (S, s2))
    | Us, _ -> Us
    | Us, (Nil, s2) -> Us
    | Us, Ss2 ->
        lowerEVar X;
        whnfRedex (whnf Us, Ss2)
    | Us, Ss2 -> whnfRedex ((U, s1), Ss2)
    | Us, Ss2 -> Us
    | Us, _ -> Us
    | Us, _ -> Us
    | Us, _ -> Us

  and lowerEVar' = function
    | G, (Pi ((D', _), V'), s') ->
        let D'' = decSub (D', s') in
        let X', U = lowerEVar' (Decl (G, D''), whnfExpandDef (V', dot1 s')) in
        (X', Lam (D'', U))
    | G, Vs' ->
        let X' = newEVar (G, EClo Vs') in
        (X', X')

  and lowerEVar1 = function
    | EVar (r, G, _, _), Vs ->
        let X', U = lowerEVar' (G, Vs) in
        let _ = r := Some U in
        X'
    | X, _ -> X

  and lowerEVar = function
    | X -> lowerEVar1 (X, whnfExpandDef (V, id))
    | EVar _ ->
        raise
          (Error
             "Typing ambiguous -- constraint of functional type cannot be \
              simplified")

  and whnfRoot = function
    | (BVar k, S), s -> (
        match bvarSub (k, s) with
        | Idx k -> (Root (BVar k, SClo (S, s)), id)
        | Exp U -> whnfRedex (whnf (U, id), (S, s)))
    | (Proj (B, i), S), s -> (
        match blockSub (B, s) with
        | B' -> (Root (Proj (B', i), SClo (S, s)), id)
        | B' -> whnfRoot ((Proj (B', i), SClo (S, s)), id)
        | Inst L -> whnfRedex (whnf (List.nth (L, i - 1), id), (S, s)))
    | (Proj (LVar ({ contents = Some B }, sk, (l, t)), i), S), s ->
        whnfRoot ((Proj (blockSub (B, comp (sk, s)), i), SClo (S, s)), id)
    | (Proj (L, i), S), s ->
        (Root (Proj (LVar (r, comp (sk, s), (l, t)), i), SClo (S, s)), id)
    | (FVar (name, V, s'), S), s ->
        (Root (FVar (name, V, comp (s', s)), SClo (S, s)), id)
    | (NSDef d, S), s -> whnfRedex (whnf (IntSyn.constDef d, id), (S, s))
    | (H, S), s -> (Root (H, SClo (S, s)), id)

  and whnf = function
    | U, s -> (U, s)
    | U, s -> (U, s)
    | Root R, s -> whnfRoot (R, s)
    | Redex (U, S), s -> whnfRedex (whnf (U, s), (S, s))
    | Us -> Us
    | AVar { contents = Some U }, s -> whnf (U, s)
    | Us -> Us
    | EVar ({ contents = Some U }, _, _, _), s -> whnf (U, s)
    | Us -> Us
    | Us -> Us
    | Us -> (
        match whnf (V, id) with
        | Pi _, _ ->
            lowerEVar X;
            whnf Us (* possible opt: call lowerEVar1 *)
        | _ -> Us)
    | EClo (U, s'), s -> whnf (U, comp (s', s))
    | Us -> Us
    | Us -> (FgnExpStd.Map.apply csfe (fun U -> EClo (U, s)), id)

  and expandDef (Root (Def d, S), s) =
    (* why the call to whnf?  isn't constDef (d) in nf? -kw *)
    whnfRedex (whnf (constDef d, id), (S, s))

  and whnfExpandDefW = function Us -> whnfExpandDefW (expandDef Us) | Us -> Us
  and whnfExpandDef Us = whnfExpandDefW (whnf Us)

  let rec newLoweredEVarW = function
    | G, (Pi ((D, _), V), s) ->
        let D' = decSub (D, s) in
        Lam (D', newLoweredEVar (Decl (G, D'), (V, dot1 s)))
    | G, Vs -> newEVar (G, EClo Vs)

  and newLoweredEVar (G, Vs) = newLoweredEVarW (G, whnfExpandDef Vs)

  let rec newSpineVarW = function
    | G, (Pi ((Dec (_, Va), _), Vr), s) ->
        let X = newLoweredEVar (G, (Va, s)) in
        App (X, newSpineVar (G, (Vr, dotEta (Exp X, s))))
    | G, _ -> Nil

  and newSpineVar (G, Vs) = newSpineVarW (G, whnfExpandDef Vs)

  let rec spineToSub = function
    | Nil, s -> s
    | App (U, S), s -> spineToSub (S, dotEta (Exp U, s))
  (* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1[s1] == W)
       then G |- V'[s'] = W
    *)

  (* FIX: this is almost certainly mis-design -kw *)

  let rec inferSpine = function
    | (Nil, _), Vs -> Vs
    | (SClo (S, s'), s), Vs -> inferSpine ((S, comp (s', s)), Vs)
    | (App (U, S), s1), (Pi (_, V2), s2) ->
        inferSpine ((S, s1), whnfExpandDef (V2, Dot (Exp (EClo (U, s1)), s2)))
  (* inferCon (C) = V  if C = c or C = d or C = sk and |- C : V *)

  (* FIX: this is almost certainly mis-design -kw *)

  let rec inferCon = function
    | Const cid -> constType cid
    | Skonst cid -> constType cid
    | Def cid -> constType cid
  (* etaExpand' (U, (V,s)) = U'

       Invariant :
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *)

  (* quite inefficient -cs *)

  (* FIX: this is almost certainly mis-design -kw *)

  let rec etaExpand' = function
    | U, (Root _, s) -> U
    | U, (Pi ((D, _), V), s) ->
        Lam
          ( decSub (D, s),
            etaExpand'
              ( Redex (EClo (U, shift), App (Root (BVar 1, Nil), Nil)),
                whnfExpandDef (V, dot1 s) ) )
  (* etaExpandRoot (Root(H, S)) = U' where H = c or H = d

       Invariant:
       If   G |- H @ S : V  where H = c or H = d
       then G |- U' : V
       and  G |- H @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *)

  (* FIX: this is almost certainly mis-design -kw *)

  let rec etaExpandRoot U =
    etaExpand' (U, inferSpine ((S, id), (inferCon H, id)))
  (* whnfEta ((U, s1), (V, s2)) = ((U', s1'), (V', s2)')

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

  let rec whnfEta (Us, Vs) = whnfEtaW (whnf Us, whnf Vs)

  and whnfEtaW = function
    | UsVs -> UsVs
    | UsVs -> UsVs
    | (U, s1), Vs2 ->
        ( ( Lam
              ( decSub (D, s2),
                Redex (EClo (U, comp (s1, shift)), App (Root (BVar 1, Nil), Nil))
              ),
            id ),
          Vs2 )
  (* Invariant:

       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V
       then U [s] = U'
       and  U' in existential normal form

       If (U, s) contain no existential variables,
       then U' in normal formal
    *)

  let rec normalizeExp Us = normalizeExpW (whnf Us)

  and normalizeExpW = function
    | U, s -> U
    | Pi (DP, U), s -> Pi (normalizeDecP (DP, s), normalizeExp (U, dot1 s))
    | U, s -> Root (H, normalizeSpine (S, s))
    | Lam (D, U), s -> Lam (normalizeDec (D, s), normalizeExp (U, dot1 s))
    | Us -> EClo Us
    | FgnExp csfe, s -> FgnExpStd.Map.apply csfe (fun U -> normalizeExp (U, s))
    | Us -> normalizeExpW (U, s)
    | Us ->
        print "Normalize  AVAR\n";
        raise (Error "")

  and normalizeSpine = function
    | Nil, s -> Nil
    | App (U, S), s -> App (normalizeExp (U, s), normalizeSpine (S, s))
    | SClo (S, s'), s -> normalizeSpine (S, comp (s', s))

  and normalizeDec = function
    | Dec (xOpt, V), s -> Dec (xOpt, normalizeExp (V, s))
    | BDec (xOpt, (c, t)), s -> BDec (xOpt, (c, normalizeSub (comp (t, s))))

  and normalizeDecP ((D, P), s) = (normalizeDec (D, s), P)

  and normalizeSub = function
    | s -> s
    | Dot (Ft, s) -> Dot (Ft, normalizeSub s)
    | Dot (Exp U, s) -> dotEta (Exp (normalizeExp (U, id)), normalizeSub s)

  let rec normalizeCtx = function
    | Null -> Null
    | Decl (G, D) -> Decl (normalizeCtx G, normalizeDec (D, id))
  (* invert s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)

  let rec invert s =
    let rec lookup = function
      | n, Shift _, p -> None
      | n, Dot (Undef, s'), p -> lookup (n + 1, s', p)
      | n, Dot (Idx k, s'), p -> if k = p then Some n else lookup (n + 1, s', p)
    in
    let rec invert'' = function
      | 0, si -> si
      | p, si -> (
          match lookup (1, s, p) with
          | Some k -> invert'' (p - 1, Dot (Idx k, si))
          | None -> invert'' (p - 1, Dot (Undef, si)))
    in
    let rec invert' = function
      | n, Shift p -> invert'' (p, Shift n)
      | n, Dot (_, s') -> invert' (n + 1, s')
    in
    invert' (0, s)
  (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G    (* and t strsub *)
       then G' |- t : G  and G' subcontext of G
    *)

  let rec strengthen = function
    | Shift n (* = 0 *), Null -> Null
    | Dot (Idx k (* k = 1 *), t), Decl (G, D) ->
        let t' = comp (t, invShift) in
        (* G |- D dec *)
        (* G' |- t' : G *)
        (* G' |- D[t'] dec *)
        Decl (strengthen (t', G), decSub (D, t'))
    | Dot (Undef, t), Decl (G, D) -> strengthen (t, G)
    | Shift n, G -> strengthen (Dot (Idx (n + 1), Shift (n + 1)), G)
  (* isId s = B

       Invariant:
       If   G |- s: G', s weakensub
       then B holds
            iff s = id, G' = G
    *)

  let rec isId' = function
    | Shift k, k' -> k = k'
    | Dot (Idx n, s'), k' -> n = k' && isId' (s', k' + 1)
    | _ -> false

  let rec isId s = isId' (s, 0)
  (* cloInv (U, w) = U[w^-1]

       Invariant:
       If G |- U : V
          G |- w : G'  w weakening subst
          U[w^-1] defined (without pruning or constraints)

       then G' |- U[w^-1] : V[w^-1]
       Effects: None
    *)

  let rec cloInv (U, w) = EClo (U, invert w)
  (* cloInv (s, w) = s o w^-1

       Invariant:
       If G |- s : G1
          G |- w : G2  s weakening subst
          s o w^-1 defined (without pruning or constraints)

       then G2 |- s o w^-1 : G1
       Effects: None
    *)

  let rec compInv (s, w) = comp (s, invert w)
  (* functions previously in the Pattern functor *)

  (* eventually, they may need to be mutually recursive with whnf *)

  (* isPatSub s = B

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for_sml all 1 <= i <= m
    *)

  let rec isPatSub = function
    | Shift k -> true
    | Dot (Idx n, s) ->
        let rec checkBVar = function
          | Shift k -> n <= k
          | Dot (Idx n', s) -> n <> n' && checkBVar s
          | Dot (Undef, s) -> checkBVar s
          | _ -> false
        in
        checkBVar s && isPatSub s
    | Dot (Undef, s) -> isPatSub s
    | _ -> false
  (* Try harder, due to bug somewhere *)

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
               and  ni <= k or ni = _ for_sml all 1 <= i <= m
    *)

  let rec mkPatSub = function
    | s -> s
    | Dot (Idx n, s) ->
        let s' = mkPatSub s in
        let rec checkBVar = function
          | Shift k -> n <= k
          | Dot (Idx n', s') -> n <> n' && checkBVar s'
          | Dot (Undef, s') -> checkBVar s'
        in
        let _ = checkBVar s' in
        Dot (Idx n, s')
    | Dot (Undef, s) -> Dot (Undef, mkPatSub s)
    | Dot (Exp U, s) ->
        (* may raise Eta *)
        let U', t' = whnf (U, id) in
        let k = etaContract (U', t', 0) in
        Dot (Idx k, mkPatSub s)
    | _ -> raise Eta

  let rec makePatSub s = try Some (mkPatSub s) with Eta -> None
  let isPatSub = isPatSub
  let makePatSub = makePatSub
  let dotEta = dotEta

  exception EtaEta

  let etaContract = fun U -> etaContract (U, id, 0)
  let whnf = whnf
  let expandDef = expandDef
  let whnfExpandDef = whnfExpandDef
  let etaExpandRoot = etaExpandRoot
  let whnfEta = whnfEta
  let lowerEVar = lowerEVar
  let newLoweredEVar = newLoweredEVar
  let newSpineVar = newSpineVar
  let spineToSub = spineToSub
  let normalize = normalizeExp
  let normalizeDec = normalizeDec
  let normalizeCtx = normalizeCtx
  let invert = invert
  let strengthen = strengthen
  let isId = isId
  let cloInv = cloInv
  let compInv = compInv
end

(* functor Whnf *)
(* Weak Head-Normal Forms *)

(* Authors: Frank Pfenning, Carsten Schuermann *)

module type WHNF = sig
  (*! structure IntSyn : INTSYN !*)
  (* Patterns *)
  val isPatSub : IntSyn.sub -> bool
  val makePatSub : IntSyn.sub -> IntSyn.sub option
  val dotEta : IntSyn.front * IntSyn.sub -> IntSyn.sub

  exception Eta

  val etaContract : IntSyn.exp -> int

  (* can raise Eta *)
  (* Weak head normalization *)
  val whnf : IntSyn.eclo -> IntSyn.eclo
  val expandDef : IntSyn.eclo -> IntSyn.eclo
  val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
  val etaExpandRoot : IntSyn.exp -> IntSyn.exp
  val whnfEta : IntSyn.eclo * IntSyn.eclo -> IntSyn.eclo * IntSyn.eclo
  val lowerEVar : IntSyn.exp -> IntSyn.exp
  val newLoweredEVar : IntSyn.dctx * IntSyn.eclo -> IntSyn.exp
  val newSpineVar : IntSyn.dctx * IntSyn.eclo -> IntSyn.spine
  val spineToSub : IntSyn.spine * IntSyn.sub -> IntSyn.sub

  (* Full normalization *)
  val normalize : IntSyn.eclo -> IntSyn.exp
  val normalizeDec : IntSyn.dec * IntSyn.sub -> IntSyn.dec
  val normalizeCtx : IntSyn.dctx -> IntSyn.dctx

  (* Inverting substitutions *)
  val invert : IntSyn.sub -> IntSyn.sub
  val strengthen : IntSyn.sub * IntSyn.dctx -> IntSyn.dctx
  val isId : IntSyn.sub -> bool
  val cloInv : IntSyn.exp * IntSyn.sub -> IntSyn.exp
  val compInv : IntSyn.sub * IntSyn.sub -> IntSyn.sub
end

(* signature WHNF *)
