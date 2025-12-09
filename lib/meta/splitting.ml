(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

module MTPSplitting (MTPGlobal : MTPGLOBAL)
   (Global : GLOBAL)
                      (*! (IntSyn : INTSYN) !*)
                      (*! (FunSyn : FUNSYN) !*)
                      (*! sharing FunSyn.IntSyn = IntSyn !*)
                      module StateSyn' : STATESYN
                      (*! sharing StateSyn'.FunSyn = FunSyn !*)
                        (*! sharing StateSyn'.IntSyn = IntSyn !*)
                      (Heuristic : HEURISTIC)
                      (MTPAbstract : MTPABSTRACT)
                      (*! sharing MTPAbstract.IntSyn = IntSyn !*)
                        sharing MTPAbstract.StateSyn = StateSyn'
                      (MTPrint : MTPRINT)
                        sharing MTPrint.StateSyn = StateSyn'
                      (Names : NAMES)            (* too be removed  -cs *)
                      (*! sharing Names.IntSyn = IntSyn !*)    (* too be removed  -cs *)
                      module Conv :CONV
                      (*! sharing Conv.IntSyn = IntSyn !*)
                      (Whnf : WHNF)
                      (*! sharing Whnf.IntSyn = IntSyn !*)
                      (TypeCheck : TYPECHECK)
                      (*! sharing TypeCheck.IntSyn = IntSyn !*)
                      (Subordinate : SUBORDINATE)
                      (*! sharing Subordinate.IntSyn = IntSyn !*)
                      module FunTypeCheck :FUNTYPECHECK
                      (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
                        sharing FunTypeCheck.StateSyn = StateSyn'
                      (Index : INDEX)
                      (*! sharing Index.IntSyn = IntSyn !*)
                      (Print : PRINT)
                      (*! sharing Print.IntSyn = IntSyn !*)
                      (Unify : UNIFY)
                      (*! sharing Unify.IntSyn = IntSyn !*)
                      (*! (CSManager : CS_MANAGER) !*)
                      (*! sharing CSManager.IntSyn = IntSyn  !*)
                        ): MTPSPLITTING =
struct
  module StateSyn = StateSyn'

  exception Error of string

  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for a given operator by applicable)
  *)
  type 'a flag =
    Active of 'a | InActive

  type operator =
    Operator of (StateSyn.State * int) * StateSyn.State flag list
                   * Heuristic.index

  local
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module H = Heuristic


    let rec makeOperator = function ((S, k), L, S.Splits n, g, I, m, true) -> (* recursive case *)
          Operator ((S, k), L, {sd=n, ind=I, c=List.length L, m=m, r=1, p=g+1})
      | ((S, k), L, S.Splits n, g, I, m, false) -> (* non-recursive case *)
          Operator ((S, k), L, {sd=n, ind=I, c=List.length L, m=m, r=0, p=g+1})

    (* aux (G, B) = L'

       Invariant:
       If   . |- G ctx
       and  G |- B tags
       then . |- L' = GxB lfctx
    *)

    let rec aux = function (I.Null, I.Null) -> I.Null
      | (I.Decl (G, D), I.Decl (B, S.Lemma _)) -> 
          I.Decl (aux (G, B), F.Prim D)
      | (G as I.Decl (_, D), B as I.Decl (_, S.Parameter (SOME l))) -> 
        let
          let F.LabelDec  (name, _, G2) = F.labelLookup l
          let (Psi', G') = aux' (G, B, List.length G2)
        in
          I.Decl (Psi', F.Block (F.CtxBlock (SOME l, G')))
        end

    and aux' (G, B, 0) = (aux (G, B), I.Null)
      | aux' (I.Decl (G, D), I.Decl (B, S.Parameter (SOME _)), n) =
        let
          let (Psi', G') = aux' (G, B, n-1)
        in
          (Psi', I.Decl (G', D))
        end



    (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
    let rec conv = function (Gs, Gs') -> 
      let
        exception Conv
        let rec conv ((I.Null, s), (I.Null, s')) = (s, s')
          | conv ((I.Decl (G, I.Dec (_, V)), s),
                  (I.Decl (G', I.Dec (_, V')), s')) =
            let
              let (s1, s1') = conv ((G, s), (G', s'))
              let ps as (s2, s2') = (I.dot1 s1, I.dot1 s1')
            in
              if Conv.conv ((V, s1), (V', s1')) then ps
              else raise Conv
            end
          | _ -> raise Conv
      in
        (conv (Gs, Gs'); true) handle Conv => false
      end



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
    and createEVarSpineW (G, Vs as (I.Uni I.Type, s)) = (I.Nil, Vs) (* s = id *)
      | createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let
          let X = I.newEVar (G, I.EClo (V1, s))
          let (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
        in
          (I.App (X, S), Vs)
        end

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    let rec createAtomConst (G, H) =
      let
        let cid = (case H
                     of (I.Const cid) => cid
                      | (I.Skonst cid) => cid)
        let V = I.constType cid
        let (S, Vs) = createEVarSpine (G, (V, I.id))
      in
        (I.Root (H, S), Vs)
      end

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    let rec createAtomBVar (G, k) =
      let
        let I.Dec (_, V) = I.ctxDec (G, k)
        let (S, Vs) = createEVarSpine (G, (V, I.id))
      in
        (I.Root (I.BVar (k), S), Vs)
      end


    (* someEVars (G, G1, s) = s'

       Invariant:
       If   |- G ctx
       and  G |- s : G'
       then G |- s' : G', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)

    let rec someEVars = function (G, nil, s) -> s
      | (G, I.Dec (_, V) :: L, s) -> 
          someEVars(G, L, I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s))


    let rec maxNumberParams a =
      let
        let rec maxNumberParams' (n) =
          if n < 0 then 0
          else
            let
              let F.LabelDec (name, G1, G2) = F.labelLookup n
              let m' = foldr (fn (I.Dec (_, V), m) =>
                              if I.targetFam V = a then m + 1 else m) 0 G2
            in
              maxNumberParams' (n-1) + m'
            end
      in
        maxNumberParams' (F.labelSize () - 1)
      end


    let rec maxNumberLocalParams = function (I.Pi ((I.Dec (_, V1), _), V2), a) -> 
        let
          let m = maxNumberLocalParams (V2, a)
        in
          if I.targetFam V1 = a then m+1
          else m
        end
      | (I.Root _, a) -> 0



    let rec maxNumberConstCases a =
          List.length (Index.lookup a)

    let rec maxNumberCases (V, a) =
      maxNumberParams a + maxNumberLocalParams (V, a) + maxNumberConstCases a

    (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)

    let rec ctxSub = function (nil, s) -> nil
      | (D :: G, s) -> I.decSub (D, s) :: ctxSub (G, I.dot1 s)



    let rec createTags = function (0, l) -> I.Null
      | (n, l) -> 
           I.Decl (createTags (n-1, l),  S.Parameter (SOME l))


    let rec createLemmaTags = function (I.Null) -> I.Null
      | (I.Decl (G, D)) -> 
           I.Decl (createLemmaTags G,  S.Lemma (S.Splits (!MTPGlobal.maxSplit)))

    (* constCases (G, (V, s), I, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)
    let rec constCases = function (G, Vs, nil, abstract, ops) -> ops
      | (G, Vs, I.Const c::Sgn, abstract, ops) -> 
        let
          let (U, Vs') = createAtomConst (G, I.Const c)
        in
          constCases (G, Vs, Sgn, abstract,
                      CSManager.trail (fn () =>
                                   (if Unify.unifiable (G, Vs, Vs')
                                      then Active (abstract U)
                                           :: ops
                                    else ops)
                                   handle  MTPAbstract.Error _ => InActive :: ops))
        end

    (* paramCases (G, (V, s), k, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in G
    *)
    let rec paramCases = function (G, Vs, 0, abstract, ops) -> ops
      | (G, Vs, k, abstract, ops) -> 
        let
          let (U, Vs') = createAtomBVar (G, k)
        in
          paramCases (G, Vs, k-1, abstract,
                      CSManager.trail (fn () =>
                                   (if Unify.unifiable (G, Vs, Vs')
                                      then Active (abstract U) :: ops
                                    else ops)
                                      handle  MTPAbstract.Error _ => InActive  :: ops))
        end


    let rec constAndParamCases ops0 (c, G, k, (V, s'), abstract)  =
          constCases (G, (V, s'), Index.lookup c, abstract,
                      paramCases (G, (V, s'), k, abstract, ops0))


    let rec metaCases (d, ops0) (c, G, k, Vs, abstract) =
      let
        let g = I.ctxLength G

        let rec select = function (0, ops) -> ops
          | (d', ops) -> 
            let
              let n = g-d'+1
              let I.Dec (_, V) = I.ctxDec (G, n)
              let ops' = if I.targetFam V = c then
                        let
                          let (U, Vs') = createAtomBVar (G, n)
                        in
                          CSManager.trail (fn () =>
                                       (if Unify.unifiable (G, Vs, Vs')
                                          then (Active (abstract U) :: ops) (* abstract state *)
                                        else ops)
                                          handle MTPAbstract.Error _ => InActive :: ops)
                        end
                      else ops
            in
              select (d'-1, ops')
            end
      in
        select (d, ops0)
      end


    (* lowerSplitDest (G, k, (V, s'), abstract) = ops'

       Invariant:
       If  G0, G |- s' : G1  G1 |- V: type
       and  k = |local parameters in G|
       and  G is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
            (it contains constant and parameter cases)
    *)
    let rec lowerSplitDest = function (G, k, (V as I.Root (I.Const c, _), s'), abstract, cases) -> 
          cases (c, G, I.ctxLength G , (V, s'), abstract)
      | (G, k, (I.Pi ((D, P), V), s'), abstract, cases) -> 
          let
            let D' = I.decSub (D, s')
          in
            lowerSplitDest (I.Decl (G, D'), k+1, (V, I.dot1 s'),
                            fun U -> abstract (I.Lam (D', U)), cases)
          end



    let rec abstractErrorLeft ((G, B), s) =
      (raise MTPAbstract.Error "Cannot split left of parameters")

    let rec abstractErrorRight ((G, B), s) =
      (raise MTPAbstract.Error "Cannot split right of parameters")



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
    let rec split ((D as I.Dec (_, V), T), sc, abstract) =
        let
          let rec split' (n, cases) =
            if n < 0 then
              let
                let ((G', B'), s', (G0, B0), _) = sc (I.Null, I.Null)
                                        (* |- G' = parameter blocks of G  ctx*)
                                        (* G' |- B' tags *)
                                        (* G' |- s' : G *)
                let rec abstract' U' =
                  let
                                        (* G' |- U' : V[s'] *)
                                        (* G' |- U'.s' : G, V[s'] *)
                    let ((G'', B''), s'') = MTPAbstract.abstractSub' ((G', B'), I.Dot (I.Exp U', s'), I.Decl (B0, T))

                    let _ = if !Global.doubleCheck then
                              let
                                let Psi'' = aux (G'',B'')
                                let _ = TypeCheck.typeCheckCtx (F.makectx Psi'')

                                let Psi = aux (I.Decl (G0, D), I.Decl (B0, T))
                                let _ = TypeCheck.typeCheckCtx (F.makectx Psi)
                              in
                                FunTypeCheck.checkSub (Psi'', s'', Psi)
                              end
                            else ()
                  in
                    abstract ((G'', B''), s'')
                  end
              in
                lowerSplitDest (G', 0, (V, s'),
                                abstract',
                                constAndParamCases cases)
              end
            else
              let
                let F.LabelDec (name, G1, G2) = F.labelLookup n
                let t = someEVars (I.Null, G1, I.id)
                                        (* . |- t : G1 *)
                let B1 = createLemmaTags (F.listToCtx G1)
                let G2t = ctxSub (G2, t)
                                        (* . |- G2 [t] ctx *)
                let length = List.length G2
                let B2 = createTags (length , n)
                                        (* G2 [t] |- B2 tags *)
                let ((G', B'), s', (G0, B0), p) = sc (Names.ctxName (F.listToCtx G2t), B2)
                                        (* . |- G' ctx *)
                                        (* G' |- B' tags *)
                                        (* G' |- s : G = G0 *)
                                        (* G0 |- B0 tags *)

                (* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *)
                let rec abstract' U' =
                                        (* G' |- U' : V[s'] *)
                  if p then (raise MTPAbstract.Error "Cannot split right of parameters")
                  else
                    let
                                        (* G' |- U.s' : G, V *)
                                        (* . |- t : G1 *)
                      let ((G'', B''), s'') = MTPAbstract.abstractSub (t, B1, (G', B'), I.Dot (I.Exp U', s'), I.Decl (B0, T))
                                        (* . |- G'' ctx *)
                                        (* G'' |- B'' tags *)
                                        (* G'' = G1'', G2', G2'' *)
                                        (* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
                      let _ = if !Global.doubleCheck then
                                let
                                  let Psi'' = aux (G'',B'')
                                  let _ = TypeCheck.typeCheckCtx (F.makectx Psi'')
                                  let Psi = aux (I.Decl (G0, D), I.Decl (B0, T))
                                  let _ = TypeCheck.typeCheckCtx (F.makectx Psi)
                                in
                                  FunTypeCheck.checkSub (Psi'', s'', Psi)
                                end
                              else ()
                    in
                      abstract ((G'', B''), s'')
                    end

                let cases' = lowerSplitDest (G', 0, (V, s'), abstract',
                                           metaCases (length, cases))
              in
                split' (n - 1, cases')
              end
        in
          split' (F.labelSize () -1, nil)
        end


    (* occursInExp (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
    let rec occursInExp = function (k, I.Uni _) -> false
      | (k, I.Pi (DP, V)) -> occursInDecP (k, DP) orelse occursInExp (k+1, V)
      | (k, I.Root (C, S)) -> occursInCon (k, C) orelse occursInSpine (k, S)
      | (k, I.Lam (D,V)) -> occursInDec (k, D) orelse occursInExp (k+1, V)
      | (k, I.FgnExp csfe) -> 
        I.FgnExpStd.fold csfe (fn (U,B) => B orelse occursInExp (k, Whnf.normalize (U, I.id))) false
      (* no case for Redex, EVar, EClo *)

    and occursInCon (k, I.BVar (k')) = (k = k')
      | occursInCon (k, I.Const _) = false
      | occursInCon (k, I.Def _) = false
      | occursInCon (k, I.Skonst _) = false
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExp (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)


    let rec isIndexInit k = false
    let rec isIndexSucc (D, isIndex) k = occursInDec (k, D) orelse isIndex (k+1)
    let rec isIndexFail (D, isIndex) k = isIndex (k+1)


    (* abstractInit S ((G', B'), s') = S'

       Invariant:
       If   |- S = (n, (G, B), (IH, OH), d, O, H, F) state
       and  |- G' ctx
       and  G' |- B' tags
       and  G' |- s' : G
       then |- S' = (n, (G', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
    let rec abstractInit (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) ((G', B'), s') =
          (if !Global.doubleCheck then TypeCheck.typeCheckCtx G' else ();
           if !Global.doubleCheck then FunTypeCheck.isFor (G', F.forSub (F, s')) else ();
          S.State (n, (G', B'), (IH, OH), d, S.orderSub (O, s'),
                   map (fn (i, F') => (i, F.forSub (F', s'))) H, F.forSub (F, s')))


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
          abstract ((I.Decl (G, Whnf.normalizeDec (D, s)),
                     I.Decl (B, S.normalizeTag (T, s))), I.dot1 s)


    let rec makeAddressInit S k = (S, k)
    let rec makeAddressCont makeAddress k = makeAddress (k+1)



    let rec occursInOrder = function (n, S.Arg (Us, Vt), k, sc) -> 
        let
          let U' = Whnf.normalize Us
        in
          if occursInExp (k, U') then SOME (n) else sc (n+1)
        end
      | (n, S.Lex Os, k, sc) -> occursInOrders (n, Os, k, sc)
      | (n, S.Simul Os, k, sc) -> occursInOrders (n, Os, k, sc)
      (* no other case should be possible by invariant *)

    and occursInOrders (n, nil, k, sc) = sc n
      | occursInOrders (n, O :: Os, k, sc) =
          occursInOrder (n, O, k, fn n' => occursInOrders (n', Os, k, sc))


    let rec inductionInit O k = occursInOrder (0, O, k, fun n -> NONE)
    let rec inductionCont induction k = induction (k+1)

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
    fun expand' (GB as (I.Null, I.Null), isIndex,
                 abstract, makeAddress, induction) =
        (fn (Gp, Bp) => ((Gp, Bp), I.Shift (I.ctxLength Gp), GB, false), nil)
      | expand' (GB as (I.Decl (G, D), I.Decl (B, T as (S.Lemma (K as S.Splits _)))),
                 isIndex, abstract, makeAddress, induction) =
        let
          let (sc, ops) =
            expand' ((G, B), isIndexSucc (D, isIndex),
                     abstractCont ((D, T), abstract),
                     makeAddressCont makeAddress,
                     inductionCont induction)
          let I.Dec (xOpt, V) = D
          let rec sc' (Gp, Bp) =
            let
              let ((G', B'), s', (G0, B0), p') = sc (Gp, Bp)
              let X = I.newEVar (G', I.EClo (V, s'))     (* G' |- X : V[s'] *)
            in
              ((G', B'), I.Dot (I.Exp (X), s'), (I.Decl (G0, D), I.Decl (B0, T)), p')        (* G' |- X.s' : G, D *)
            end
          let ops' = if not (isIndex 1) andalso (S.splitDepth K) > 0
                       then
                         let
                           let a = I.targetFam V
                         in
                           makeOperator (makeAddress 1, split ((D, T), sc, abstract), K, I.ctxLength G,
                                         induction 1,  maxNumberCases (V, a), Subordinate.below (a, a))
                           :: ops
                         end
                     else ops
        in
          (sc', ops')
        end
      | expand' ((I.Decl (G, D), I.Decl (B, T as (S.Lemma (S.RL)))), isIndex,
                 abstract, makeAddress, induction) =
        let
          let (sc, ops) =
            expand' ((G, B), isIndexSucc (D, isIndex),
                     abstractCont ((D, T), abstract),
                     makeAddressCont makeAddress,
                     inductionCont induction)
          let I.Dec (xOpt, V) = D
          let rec sc' (Gp, Bp) =
            let
              let ((G', B'), s', (G0, B0), p') = sc (Gp, Bp)
              let X = I.newEVar (G', I.EClo (V, s'))
            in
              ((G', B'), I.Dot (I.Exp (X), s'), (I.Decl (G0, D), I.Decl (B0, T)), p')
            end
        in
          (sc', ops)
        end
      | expand' ((I.Decl (G, D), I.Decl (B, T as (S.Lemma (S.RLdone)))), isIndex,
                 abstract, makeAddress, induction) =
        let
          let (sc, ops) =
            expand' ((G, B), isIndexSucc (D, isIndex),
                     abstractCont ((D, T), abstract),
                     makeAddressCont makeAddress,
                     inductionCont induction)
          let I.Dec (xOpt, V) = D
          let rec sc' (Gp, Bp) =
            let
              let ((G', B'), s', (G0, B0), p') = sc (Gp, Bp)
              let X = I.newEVar (G', I.EClo (V, s'))
            in
              ((G', B'), I.Dot (I.Exp (X), s'), (I.Decl (G0, D), I.Decl (B0, T)), p')
            end
        in
          (sc', ops)
        end
      | expand' ((I.Decl (G, D), I.Decl (B, T as S.Parameter (SOME _))), isIndex,
                 abstract, makeAddress, induction) =
        let
          let (sc, ops) =
            expand' ((G, B), isIndexSucc (D, isIndex),
                     abstractErrorLeft,
                     makeAddressCont makeAddress,
                     inductionCont induction)
          let I.Dec (xOpt, V) = D
          let rec sc' (Gp, Bp) =
            let
              let ((G', B'), s', (G0, B0), _) = sc (Gp, Bp)
            in
              ((I.Decl (G', Names.decName (G', I.decSub (D, s'))), I.Decl (B', T)),
               I.dot1 s', (I.Decl (G0, D), I.Decl (B0, T)), true)
            end

        in
          (sc', ops)
        end
    (* no case of (I.Decl (G, D), I.Decl (G, S.Parameter NONE)) *)


    (* expand (S) = ops'

       Invariant:
       If   |- S state
       then ops' is a list of all possiblie splitting operators
    *)
    let rec expand (S0 as S.State (n, (G0, B0), _, _, O, _, _)) =
      let
        let _ = if !Global.doubleCheck then FunTypeCheck.isState S0 else ()
        let (_, ops) =
          expand' ((G0, B0), isIndexInit, abstractInit S0, makeAddressInit S0,  inductionInit O)
      in
        ops
      end

    (* index (Op) = k

       Invariant:
       If   Op = (_, Sl)
       then k = |Sl|
    *)
    let rec index (Operator ((S, index), Sl, {c=k, ...})) = k


    let rec compare (Operator (_, _, I1), Operator (_, _, I2)) =
          H.compare (I1, I2)


    (* isInActive (F) = B

       Invariant:
       B holds iff F is inactive
    *)
    let rec isInActive = function (Active _) -> false
      | (InActive) -> true


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
      map (fn (Active S) =>
               (if (!Global.doubleCheck) then FunTypeCheck.isState S else ();
                S)

            | InActive => raise Error "Not applicable: leftover constraints")
      Sl


    (* menu (Op) = s'

       Invariant:
       If   Op = ((S, i), Sl)  and  S is named
       then s' is a string describing the operation in plain text

       (menu should hence be only called on operators which have
        been calculated from a named state)
    *)
    let rec menu (Op as Operator ((S.State (n, (G, B), (IH, OH), d, O, H, F), i), Sl, I)) =
        let
          let rec active = function (nil, n) -> n
            | (InActive :: L, n) -> active (L, n)
            | ((Active _) :: L, n) -> active (L, n+1)

          let rec inactive = function (nil, n) -> n
            | (InActive :: L, n) -> inactive (L, n+1)
            | ((Active _) :: L, n) -> inactive (L, n)

          let rec casesToString = function 0 -> "zero cases"
            | 1 -> "1 case"
            | n -> (Int.toString n) ^ " cases"



          let rec flagToString = function (_, 0) -> ""
            | (n, m) -> " [active: " ^(Int.toString n) ^
                " inactive: " ^ (Int.toString m) ^ "]"
        in
          "Splitting : " ^ Print.decToString (G, I.ctxDec (G, i)) ^
          " " ^ (H.indexToString I) ^
           (flagToString (active (Sl, 0), inactive (Sl, 0))) ^ ""
        end

  in
    let expand = expand
    let menu = menu
    let applicable = applicable
    let apply = apply
    let index = index
    let compare = compare
  end (* local *)
end;; (* functor Splitting *)
