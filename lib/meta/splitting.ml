open Basis ;; 
(* Splitting : Version 1.3 *)

(* Author: Carsten Schuermann *)

module type MTPSPLITTING = sig
  module StateSyn : Statesyn.State.STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.state -> operator list
  val applicable : operator -> bool
  val apply : operator -> StateSyn.state list
  val menu : operator -> string
  val index : operator -> int
  val compare : operator * operator -> order
end

(* signature MTPSPLITTING *)
(* Splitting : Version 1.3 *)

(* Author: Carsten Schuermann *)

module MTPSplitting
    (MTPGlobal : Global.MTPGLOBAL)
    (Global : Global.GLOBAL)
    (StateSyn' : Statesyn.State.STATESYN)
    (Heuristic : Heuristic.HEURISTIC)
    (MTPAbstract : Abstract.MTPABSTRACT)
    (MTPrint : Mtprint.MTPRINT)
    (Names : Names.NAMES)
    (Conv : Conv.CONV)
    (Whnf : Whnf.WHNF)
    (TypeCheck : Typecheck.TYPECHECK)
    (Subordinate : Subordinate.SUBORDINATE)
    (FunTypeCheck : Funtypecheck.FUNTYPECHECK)
    (Index : Index.INDEX)
    (Print : Print.PRINT)
    (Unify : Unify.UNIFY) : MTPSPLITTING = struct
  module StateSyn = StateSyn'

  exception Error of string
  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     "Active", and cases where there were
     leftover constraints after "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for_sml a given operator by applicable)
  *)

  type 'a flag = Active of 'a | InActive

  type operator =
    | Operator of
        (StateSyn.state * int) * StateSyn.state flag list * Heuristic.index

  type operator = operator

  module I = IntSyn
  module F = FunSyn
  module S = StateSyn
  module H = Heuristic

  let rec makeOperator = function
    | (S, k), L, S.Splits n, g, I, m, true ->
        Operator
          ( (S, k),
            L,
            { sd = n; ind = I; c = List.length L; m; r = 1; p = g + 1 } )
    | (S, k), L, S.Splits n, g, I, m, false ->
        Operator
          ( (S, k),
            L,
            { sd = n; ind = I; c = List.length L; m; r = 0; p = g + 1 } )
  (* aux (G, B) = L'

       Invariant:
       If   . |- G ctx
       and  G |- B tags
       then . |- L' = GxB lfctx
    *)

  let rec aux = function
    | I.Null, I.Null -> I.Null
    | I.Decl (G, D), I.Decl (B, S.Lemma _) -> I.Decl (aux (G, B), F.Prim D)
    | G, B ->
        let (F.LabelDec (name, _, G2)) = F.labelLookup l in
        let Psi', G' = aux' (G, B, List.length G2) in
        I.Decl (Psi', F.Block (F.CtxBlock (Some l, G')))

  and aux' = function
    | G, B, 0 -> (aux (G, B), I.Null)
    | I.Decl (G, D), I.Decl (B, S.Parameter (Some _)), n ->
        let Psi', G' = aux' (G, B, n - 1) in
        (Psi', I.Decl (G', D))
  (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)

  let rec conv (Gs, Gs') =
    let exception Conv in
    let rec conv = function
      | (I.Null, s), (I.Null, s') -> (s, s')
      | (I.Decl (G, I.Dec (_, V)), s), (I.Decl (G', I.Dec (_, V')), s') ->
          let s1, s1' = conv ((G, s), (G', s')) in
          let ps = (I.dot1 s1, I.dot1 s1') in
          if Conv.conv ((V, s1), (V', s1')) then ps else raise Conv
      | _ -> raise Conv
    in
    try
      conv (Gs, Gs');
      true
    with Conv -> false
  (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)

  let rec createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)

  and createEVarSpineW = function
    | G, Vs -> (I.Nil, Vs)
    | G, Vs -> (I.Nil, Vs)
    | G, (I.Pi ((D, _), V2), s) ->
        let X = I.newEVar (G, I.EClo (V1, s)) in
        let S, Vs = createEVarSpine (G, (V2, I.Dot (I.Exp X, s))) in
        (I.App (X, S), Vs)
  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomConst (G, H) =
    let cid = match H with I.Const cid -> cid | I.Skonst cid -> cid in
    let V = I.constType cid in
    let S, Vs = createEVarSpine (G, (V, I.id)) in
    (I.Root (H, S), Vs)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)

  let rec createAtomBVar (G, k) =
    let (I.Dec (_, V)) = I.ctxDec (G, k) in
    let S, Vs = createEVarSpine (G, (V, I.id)) in
    (I.Root (I.BVar k, S), Vs)
  (* someEVars (G, G1, s) = s'

       Invariant:
       If   |- G ctx
       and  G |- s : G'
       then G |- s' : G', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)

  let rec someEVars = function
    | G, [], s -> s
    | G, I.Dec (_, V) :: L, s ->
        someEVars (G, L, I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s))

  let rec maxNumberParams a =
    let rec maxNumberParams' n =
      if n < 0 then 0
      else
        let (F.LabelDec (name, G1, G2)) = F.labelLookup n in
        let m' =
          foldr
            (fun (I.Dec (_, V), m) -> if I.targetFam V = a then m + 1 else m)
            0 G2
        in
        maxNumberParams' (n - 1) + m'
    in
    maxNumberParams' (F.labelSize () - 1)

  let rec maxNumberLocalParams = function
    | I.Pi ((I.Dec (_, V1), _), V2), a ->
        let m = maxNumberLocalParams (V2, a) in
        if I.targetFam V1 = a then m + 1 else m
    | I.Root _, a -> 0

  let rec maxNumberConstCases a = List.length (Index.lookup a)

  let rec maxNumberCases (V, a) =
    maxNumberParams a + maxNumberLocalParams (V, a) + maxNumberConstCases a
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)

  let rec ctxSub = function
    | [], s -> []
    | D :: G, s -> I.decSub (D, s) :: ctxSub (G, I.dot1 s)

  let rec createTags = function
    | 0, l -> I.Null
    | n, l -> I.Decl (createTags (n - 1, l), S.Parameter (Some l))

  let rec createLemmaTags = function
    | I.Null -> I.Null
    | I.Decl (G, D) ->
        I.Decl (createLemmaTags G, S.Lemma (S.Splits !MTPGlobal.maxSplit))
  (* constCases (G, (V, s), I, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)

  let rec constCases = function
    | G, Vs, [], abstract, ops -> ops
    | G, Vs, I.Const c :: Sgn, abstract, ops ->
        let U, Vs' = createAtomConst (G, I.Const c) in
        constCases
          ( G,
            Vs,
            Sgn,
            abstract,
            Cs.CSManager.trail (fun () ->
                try
                  if Unify.unifiable (G, Vs, Vs') then
                    Active (abstract U) :: ops
                  else ops
                with MTPAbstract.Error _ -> InActive :: ops) )
  (* paramCases (G, (V, s), k, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in G
    *)

  let rec paramCases = function
    | G, Vs, 0, abstract, ops -> ops
    | G, Vs, k, abstract, ops ->
        let U, Vs' = createAtomBVar (G, k) in
        paramCases
          ( G,
            Vs,
            k - 1,
            abstract,
            Cs.CSManager.trail (fun () ->
                try
                  if Unify.unifiable (G, Vs, Vs') then
                    Active (abstract U) :: ops
                  else ops
                with MTPAbstract.Error _ -> InActive :: ops) )

  let rec constAndParamCases ops0 (c, G, k, (V, s'), abstract) =
    constCases
      ( G,
        (V, s'),
        Index.lookup c,
        abstract,
        paramCases (G, (V, s'), k, abstract, ops0) )

  let rec metaCases (d, ops0) (c, G, k, Vs, abstract) =
    let g = I.ctxLength G in
    let rec select = function
      | 0, ops -> ops
      | d', ops ->
          let n = g - d' + 1 in
          let (I.Dec (_, V)) = I.ctxDec (G, n) in
          let ops' =
            if I.targetFam V = c then
              let U, Vs' = createAtomBVar (G, n) in
              Cs.CSManager.trail (fun () ->
                  try
                    if Unify.unifiable (G, Vs, Vs') then
                      Active (abstract U) :: ops (* abstract state *)
                    else ops
                  with MTPAbstract.Error _ -> InActive :: ops)
            else ops
          in
          select (d' - 1, ops')
    in
    select (d, ops0)
  (* lowerSplitDest (G, k, (V, s'), abstract) = ops'

       Invariant:
       If  G0, G |- s' : G1  G1 |- V: type
       and  k = |local parameters in G|
       and  G is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
            (it contains constant and parameter cases)
    *)

  let rec lowerSplitDest = function
    | G, k, (V, s'), abstract, cases ->
        cases (c, G, I.ctxLength G, (V, s'), abstract)
    | G, k, (I.Pi ((D, P), V), s'), abstract, cases ->
        let D' = I.decSub (D, s') in
        lowerSplitDest
          ( I.Decl (G, D'),
            k + 1,
            (V, I.dot1 s'),
            fun U -> (abstract (I.Lam (D', U)), cases) )

  let rec abstractErrorLeft ((G, B), s) =
    raise (MTPAbstract.Error "Cannot split left of parameters")

  let rec abstractErrorRight ((G, B), s) =
    raise (MTPAbstract.Error "Cannot split right of parameters")
  (* split (x:D, sc, B, abstract) = cases'

       Invariant :
       If   |- G ctx
       and  G |- B tags
       and  G |- D : L
       then sc is a function, which maps
                Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)

       then cases' = (S1, ... Sn) are cases of the split
    *)

  let rec split ((D, T), sc, abstract) =
    let rec split' (n, cases) =
      if n < 0 then
        (* |- G' = parameter blocks of G  ctx*)
        (* G' |- B' tags *)
        (* G' |- s' : G *)
        let (G', B'), s', (G0, B0), _ = sc (I.Null, I.Null) in
        let rec abstract' U' =
          (* G' |- U' : V[s'] *)
          (* G' |- U'.s' : G, V[s'] *)
          let (G'', B''), s'' =
            MTPAbstract.abstractSub'
              ((G', B'), I.Dot (I.Exp U', s'), I.Decl (B0, T))
          in
          let _ =
            if !Global.doubleCheck then
              let Psi'' = aux (G'', B'') in
              let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
              let Psi = aux (I.Decl (G0, D), I.Decl (B0, T)) in
              let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
              FunTypeCheck.checkSub (Psi'', s'', Psi)
            else ()
          in
          abstract ((G'', B''), s'')
        in
        lowerSplitDest (G', 0, (V, s'), abstract', constAndParamCases cases)
      else
        (* . |- t : G1 *)
        (* . |- G2 [t] ctx *)
        (* G2 [t] |- B2 tags *)
        (* . |- G' ctx *)
        (* G' |- B' tags *)
        (* G' |- s : G = G0 *)
        (* G0 |- B0 tags *)
        (* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *)
        let (F.LabelDec (name, G1, G2)) = F.labelLookup n in
        let t = someEVars (I.Null, G1, I.id) in
        let B1 = createLemmaTags (F.listToCtx G1) in
        let G2t = ctxSub (G2, t) in
        let length = List.length G2 in
        let B2 = createTags (length, n) in
        let (G', B'), s', (G0, B0), p =
          sc (Names.ctxName (F.listToCtx G2t), B2)
        in
        let rec abstract' U' =
          (* G' |- U' : V[s'] *)
          if p then raise (MTPAbstract.Error "Cannot split right of parameters")
          else
            (* G' |- U.s' : G, V *)
            (* . |- t : G1 *)
            (* . |- G'' ctx *)
            (* G'' |- B'' tags *)
            (* G'' = G1'', G2', G2'' *)
            (* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
            let (G'', B''), s'' =
              MTPAbstract.abstractSub
                (t, B1, (G', B'), I.Dot (I.Exp U', s'), I.Decl (B0, T))
            in
            let _ =
              if !Global.doubleCheck then
                let Psi'' = aux (G'', B'') in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi'') in
                let Psi = aux (I.Decl (G0, D), I.Decl (B0, T)) in
                let _ = TypeCheck.typeCheckCtx (F.makectx Psi) in
                FunTypeCheck.checkSub (Psi'', s'', Psi)
              else ()
            in
            abstract ((G'', B''), s'')
        in
        let cases' =
          lowerSplitDest (G', 0, (V, s'), abstract', metaCases (length, cases))
        in
        split' (n - 1, cases')
    in
    split' (F.labelSize () - 1, [])
  (* occursInExp (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)

  let rec occursInExp = function
    | k, I.Uni _ -> false
    | k, I.Pi (DP, V) -> occursInDecP (k, DP) || occursInExp (k + 1, V)
    | k, I.Root (C, S) -> occursInCon (k, C) || occursInSpine (k, S)
    | k, I.Lam (D, V) -> occursInDec (k, D) || occursInExp (k + 1, V)
    | k, I.FgnExp csfe ->
        I.FgnExpStd.fold csfe
          (fun (U, B) -> B || occursInExp (k, Whnf.normalize (U, I.id)))
          false

  and occursInCon = function
    | k, I.BVar k' -> k = k'
    | k, I.Const _ -> false
    | k, I.Def _ -> false
    | k, I.Skonst _ -> false

  and occursInSpine = function
    | _, I.Nil -> false
    | k, I.App (U, S) -> occursInExp (k, U) || occursInSpine (k, S)

  and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
  and occursInDecP (k, (D, _)) = occursInDec (k, D)

  let rec isIndexInit k = false
  let rec isIndexSucc (D, isIndex) k = occursInDec (k, D) || isIndex (k + 1)
  let rec isIndexFail (D, isIndex) k = isIndex (k + 1)
  (* abstractInit S ((G', B'), s') = S'

       Invariant:
       If   |- S = (n, (G, B), (IH, OH), d, O, H, F) state
       and  |- G' ctx
       and  G' |- B' tags
       and  G' |- s' : G
       then |- S' = (n, (G', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)

  let rec abstractInit S ((G', B'), s') =
    if !Global.doubleCheck then TypeCheck.typeCheckCtx G' else ();
    if !Global.doubleCheck then FunTypeCheck.isFor (G', F.forSub (F, s'))
    else ();
    S.State
      ( n,
        (G', B'),
        (IH, OH),
        d,
        S.orderSub (O, s'),
        map (fun (i, F') -> (i, F.forSub (F', s'))) H,
        F.forSub (F, s') )
  (* abstractCont ((x:V, T), abstract) = abstract'

       Invariant:
       If   |- G ctx
       and  G |- V : type
       and  G |- B tags
       and  abstract is an abstraction function which maps
                    (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G, D)
                 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
                    (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : G)
                 to S'               (|- S' state)
    *)

  let rec abstractCont ((D, T), abstract) ((G, B), s) =
    abstract
      ( (I.Decl (G, Whnf.normalizeDec (D, s)), I.Decl (B, S.normalizeTag (T, s))),
        I.dot1 s )

  let rec makeAddressInit S k = (S, k)
  let rec makeAddressCont makeAddress k = makeAddress (k + 1)

  let rec occursInOrder = function
    | n, S.Arg (Us, Vt), k, sc ->
        let U' = Whnf.normalize Us in
        if occursInExp (k, U') then Some n else sc (n + 1)
    | n, S.Lex Os, k, sc -> occursInOrders (n, Os, k, sc)
    | n, S.Simul Os, k, sc -> occursInOrders (n, Os, k, sc)

  and occursInOrders = function
    | n, [], k, sc -> sc n
    | n, O :: Os, k, sc ->
        occursInOrder (n, O, k, fun n' -> occursInOrders (n', Os, k, sc))

  let rec inductionInit O k = occursInOrder (0, O, k, fun n -> None)
  let rec inductionCont induction k = induction (k + 1)
  (* expand' ((G, B), isIndex, abstract, makeAddress) = (sc', ops')

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
       and  ops' is a list of splitting operators

       Optimization possible :
         instead of reconstructin (G, B) as the result of sc, just take (G, B)
    *)

  let rec expand' = function
    | GB, isIndex, abstract, makeAddress, induction ->
        fun (Gp, Bp) -> (((Gp, Bp), I.Shift (I.ctxLength Gp), GB, false), [])
    | GB, isIndex, abstract, makeAddress, induction ->
        let sc, ops =
          expand'
            ( (G, B),
              isIndexSucc (D, isIndex),
              abstractCont ((D, T), abstract),
              makeAddressCont makeAddress,
              inductionCont induction )
        in
        let (I.Dec (xOpt, V)) = D in
        let rec sc' (Gp, Bp) =
          (* G' |- X : V[s'] *)
          let (G', B'), s', (G0, B0), p' = sc (Gp, Bp) in
          let X = I.newEVar (G', I.EClo (V, s')) in
          ((G', B'), I.Dot (I.Exp X, s'), (I.Decl (G0, D), I.Decl (B0, T)), p')
          (* G' |- X.s' : G, D *)
        in
        let ops' =
          if (not (isIndex 1)) && S.splitDepth K > 0 then
            let a = I.targetFam V in
            makeOperator
              ( makeAddress 1,
                split ((D, T), sc, abstract),
                K,
                I.ctxLength G,
                induction 1,
                maxNumberCases (V, a),
                Subordinate.below (a, a) )
            :: ops
          else ops
        in
        (sc', ops')
    | (I.Decl (G, D), I.Decl (B, T)), isIndex, abstract, makeAddress, induction
      ->
        let sc, ops =
          expand'
            ( (G, B),
              isIndexSucc (D, isIndex),
              abstractCont ((D, T), abstract),
              makeAddressCont makeAddress,
              inductionCont induction )
        in
        let (I.Dec (xOpt, V)) = D in
        let rec sc' (Gp, Bp) =
          let (G', B'), s', (G0, B0), p' = sc (Gp, Bp) in
          let X = I.newEVar (G', I.EClo (V, s')) in
          ((G', B'), I.Dot (I.Exp X, s'), (I.Decl (G0, D), I.Decl (B0, T)), p')
        in
        (sc', ops)
    | (I.Decl (G, D), I.Decl (B, T)), isIndex, abstract, makeAddress, induction
      ->
        let sc, ops =
          expand'
            ( (G, B),
              isIndexSucc (D, isIndex),
              abstractCont ((D, T), abstract),
              makeAddressCont makeAddress,
              inductionCont induction )
        in
        let (I.Dec (xOpt, V)) = D in
        let rec sc' (Gp, Bp) =
          let (G', B'), s', (G0, B0), p' = sc (Gp, Bp) in
          let X = I.newEVar (G', I.EClo (V, s')) in
          ((G', B'), I.Dot (I.Exp X, s'), (I.Decl (G0, D), I.Decl (B0, T)), p')
        in
        (sc', ops)
    | (I.Decl (G, D), I.Decl (B, T)), isIndex, abstract, makeAddress, induction
      ->
        let sc, ops =
          expand'
            ( (G, B),
              isIndexSucc (D, isIndex),
              abstractErrorLeft,
              makeAddressCont makeAddress,
              inductionCont induction )
        in
        let (I.Dec (xOpt, V)) = D in
        let rec sc' (Gp, Bp) =
          let (G', B'), s', (G0, B0), _ = sc (Gp, Bp) in
          ( (I.Decl (G', Names.decName (G', I.decSub (D, s'))), I.Decl (B', T)),
            I.dot1 s',
            (I.Decl (G0, D), I.Decl (B0, T)),
            true )
        in
        (sc', ops)
  (* no case of (I.Decl (G, D), I.Decl (G, S.Parameter NONE)) *)

  (* expand (S) = ops'

       Invariant:
       If   |- S state
       then ops' is a list of all possiblie splitting operators
    *)

  let rec expand S0 =
    let _ = if !Global.doubleCheck then FunTypeCheck.isState S0 else () in
    let _, ops =
      expand'
        ( (G0, B0),
          isIndexInit,
          abstractInit S0,
          makeAddressInit S0,
          inductionInit O )
    in
    ops
  (* index (Op) = k

       Invariant:
       If   Op = (_, Sl)
       then k = |Sl|
    *)

  let rec index (Operator ((S, index), Sl, { c = k; _ })) = k
  let rec compare (Operator (_, _, I1), Operator (_, _, I2)) = H.compare (I1, I2)
  (* isInActive (F) = B

       Invariant:
       B holds iff F is inactive
    *)

  let rec isInActive = function Active _ -> false | InActive -> true
  (* applicable (Op) = B'

       Invariant:
       If   Op = (_, Sl)
       then B' holds iff Sl does not contain inactive states
    *)

  let rec applicable (Operator (_, Sl, I)) = not (List.exists isInActive Sl)
  (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)

  let rec apply (Operator (_, Sl, I)) =
    map
      (function
        | Active S ->
            if !Global.doubleCheck then FunTypeCheck.isState S else ();
            S
        | InActive -> raise (Error "Not applicable: leftover constraints"))
      Sl
  (* menu (Op) = s'

       Invariant:
       If   Op = ((S, i), Sl)  and  S is named
       then s' is a string describing the operation in plain text

       (menu should hence be only called on operators which have
        been calculated from a named state)
    *)

  let rec menu Op =
    let rec active = function
      | [], n -> n
      | InActive :: L, n -> active (L, n)
      | Active _ :: L, n -> active (L, n + 1)
    in
    let rec inactive = function
      | [], n -> n
      | InActive :: L, n -> inactive (L, n + 1)
      | Active _ :: L, n -> inactive (L, n)
    in
    let rec casesToString = function
      | 0 -> "zero cases"
      | 1 -> "1 case"
      | n -> Int.toString n ^ " cases"
    in
    let rec flagToString = function
      | _, 0 -> ""
      | n, m ->
          " [active: " ^ Int.toString n ^ " inactive: " ^ Int.toString m ^ "]"
    in
    "Splitting : "
    ^ Print.decToString (G, I.ctxDec (G, i))
    ^ " " ^ H.indexToString I
    ^ flagToString (active (Sl, 0), inactive (Sl, 0))
    ^ ""

  let expand = expand
  let menu = menu
  let applicable = applicable
  let apply = apply
  let index = index
  let compare = compare
  (* local *)
end

(* functor Splitting *)
