(* Meta Abstraction *)

(* Author: Carsten Schuermann *)

module MetaAbstract
    (Global : GLOBAL)
    (MetaSyn' : METASYN)
    (MetaGlobal : METAGLOBAL)
    (Abstract : ABSTRACT)
    (ModeTable : MODETABLE)
    (Whnf : WHNF)
    (Print : PRINT)
    (Constraints : CONSTRAINTS)
    (Unify : UNIFY)
    (Names : NAMES)
    (TypeCheck : TYPECHECK)
    (Subordinate : SUBORDINATE) : METAABSTRACT = struct
  module MetaSyn = MetaSyn'

  exception Error of string

  module I = IntSyn
  module S = Stream
  module M = MetaSyn
  module C = Constraints
  (* Invariants? *)

  (* Definition: Mode dependency order

       A pair ((G, M), V) is in mode dependency order iff
           G |- V : type
           G |- M modes
       and G = G0+, G1-, G1+,  ... G0-
       and V = {xn:Vn} ..{x1:V1}P0
       where G0+ collects all +variables when traversing P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing P0 in order.
    *)

  type var =
    | EV of
        I.exp option ref (* Var ::= EVar <r_, V, St>       *)
        * I.exp
        * MetaSyn.mode
    | BV
  (*       | BV                     *)

  (*--------------------------------------------------------------------*)

  (* First section: Collecting EVars and BVars in mode dependency order *)

  (*--------------------------------------------------------------------*)

  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)

  let rec checkEmpty = function
    | [] -> ()
    | Cnstr -> (
        match C.simplify Cnstr with
        | [] -> ()
        | _ -> raise (Error "Unresolved constraints"))
  (* Let G x A: .      x .            = .
       (G, V) x (A, BVar)    = (G x A), V
       (G, V) x (A, EVar V') = (G, V x A), V'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, V, m)
       ? then  . |- V = {G x A'}.V' : type
       ? where G x A' |- V' : type

       We write A ||- U if all EVars and BVars of U are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for_sml the other syntactic categories.
    *)

  (* typecheck ((G, M), V) = ()

       Invariant:
       If G |- V : type
       then typecheck returns ()
       else TypeCheck.Error is raised
    *)

  let rec typecheck (M.Prefix (G, M, B), V) =
    TypeCheck.typeCheck (G, (V, I.Uni I.Type))
  (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)

  let rec modeEq = function
    | ModeSyn.Marg (ModeSyn.Plus, _), M.Top -> true
    | ModeSyn.Marg (ModeSyn.Minus, _), M.Bot -> true
    | _ -> false
  (* atxLookup (atx, r)  = Eopt'

       Invariant:
       If   r exists in EV (V)
       then Eopt' = SOME EV and . |- V : type
       else Eopt' = NONE
    *)

  let rec atxLookup = function
    | I.Null, _ -> None
    | I.Decl (M, BV), r -> atxLookup (M, r)
    | I.Decl (M, E), r -> if r = r' then Some E else atxLookup (M, r)
  (* raiseType (k, G, V) = {{G'}} V

       Invariant:
       If G |- V : L
          G = G0, G'  (so k <= |G|)
       then  G0 |- {{G'}} V : L
             |G'| = k

       All abstractions are potentially dependent.
    *)

  let rec raiseType = function
    | 0, G, V -> V
    | depth, I.Decl (G, D), V -> raiseType (depth - 1, G, I.Pi ((D, I.Maybe), V))
  (* weaken (depth,  G, a) = (w')
    *)

  let rec weaken = function
    | 0, G, a -> I.id
    | depth, I.Decl (G', D), a ->
        let w' = weaken (depth - 1, G', a) in
        if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
        else I.comp (w', I.shift)
  (* countPi V = n'

       If   G |- x : V
       and  V = {G'} V'
       then |G'| = n'
    *)

  (* V in nf or enf? -fp *)

  let rec countPi V =
    let rec countPi' = function
      | I.Root _, n -> n
      | I.Pi (_, V), n -> countPi' (V, n + 1)
      | I.EClo (V, _), n -> countPi' (V, n)
    in
    countPi' (V, 0)
  (* collectExp (lG0, G, (U, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for_sml the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- U : V
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- U [s]
    *)

  let rec collectExp (lG0, G, Us, mode, Adepth) =
    collectExpW (lG0, G, Whnf.whnf Us, mode, Adepth)

  and collectExpW = function
    | lG0, G, (I.Uni _, s), mode, Adepth -> Adepth
    | lG0, G, (I.Pi ((D, _), V), s), mode, Adepth ->
        collectExp
          ( lG0,
            I.Decl (G, I.decSub (D, s)),
            (V, I.dot1 s),
            mode,
            collectDec (lG0, G, (D, s), mode, Adepth) )
    | lG0, G, (I.Lam (D, U), s), mode, Adepth ->
        collectExp
          ( lG0,
            I.Decl (G, I.decSub (D, s)),
            (U, I.dot1 s),
            mode,
            collectDec (lG0, G, (D, s), mode, Adepth) )
    | lG0, G, Us, mode, Adepth ->
        let l = I.ctxLength G in
        if k = l + depth - lG0 && depth > 0 then
          (* invariant: all variables (EV or BV) in V already seen! *)
          let (I.Dec (_, V)) = I.ctxDec (G, k) in
          collectSpine (lG0, G, (S, s), mode, (I.Decl (A, BV), depth - 1))
        else collectSpine (lG0, G, (S, s), mode, Adepth)
    | lG0, G, (I.Root (C, S), s), mode, Adepth ->
        collectSpine (lG0, G, (S, s), mode, Adepth)
    | lG0, G, (I.EVar (r, GX, V, cnstrs), s), mode, Adepth -> (
        match atxLookup (A, r) with
        | None ->
            (* lGp' >= 0 *)
            (* lGp'' >= 0 *)
            (* invariant: all variables (EV) in Vraised already seen *)
            let _ = checkEmpty !cnstrs in
            let lGp' = I.ctxLength GX - lG0 + depth in
            let w = weaken (lGp', GX, I.targetFam V) in
            let iw = Whnf.invert w in
            let GX' = Whnf.strengthen (iw, GX) in
            let lGp'' = I.ctxLength GX' - lG0 + depth in
            let Vraised = raiseType (lGp'', GX', I.EClo (V, iw)) in
            let X' = I.newEVar (GX', I.EClo (V, iw)) in
            let _ = Unify.instantiateEVar (r, I.EClo (X', w), []) in
            collectSub
              ( lG0,
                G,
                lGp'',
                s,
                mode,
                (I.Decl (A, EV (r', Vraised, mode)), depth) )
        | Some (EV (_, V, _)) ->
            let lGp' = countPi V in
            collectSub (lG0, G, lGp', s, mode, Adepth))
    | lGO, G, (I.FgnExp csfe, s), mode, Adepth ->
        I.FgnExpStd.fold csfe
          (fun (U, Adepth') -> collectExp (lGO, G, (U, s), mode, Adepth'))
          Adepth

  and collectSub = function
    | _, _, 0, _, _, Adepth -> Adepth
    | lG0, G, lG', I.Shift k, mode, Adepth ->
        collectSub
          (lG0, G, lG', I.Dot (I.Idx (k + 1), I.Shift (k + 1)), mode, Adepth)
    | lG0, G, lG', I.Dot (I.Idx k, s), mode, Adepth ->
        collectSub (lG0, G, lG' - 1, s, mode, Adepth)
    | lG0, G, lG', I.Dot (I.Exp U, s), mode, Adepth ->
        collectSub
          ( lG0,
            G,
            lG' - 1,
            s,
            mode,
            collectExp (lG0, G, (U, I.id), mode, Adepth) )

  and collectSpine = function
    | lG0, G, (I.Nil, _), mode, Adepth -> Adepth
    | lG0, G, (I.SClo (S, s'), s), mode, Adepth ->
        collectSpine (lG0, G, (S, I.comp (s', s)), mode, Adepth)
    | lG0, G, (I.App (U, S), s), mode, Adepth ->
        collectSpine
          (lG0, G, (S, s), mode, collectExp (lG0, G, (U, s), mode, Adepth))

  and collectDec (lG0, G, (I.Dec (x, V), s), mode, Adepth) =
    collectExp (lG0, G, (V, s), mode, Adepth)
  (* collectModeW (lG0, G, modeIn, modeRec, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for_sml the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L        V[s] in whnf
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all EVars/BVars marked with modeIn in V and
                modeRec
    *)

  let rec collectModeW = function
    | lG0, G, modeIn, modeRec, (I.Root (I.Const cid, S), s), Adepth ->
        let rec collectModeW' = function
          | ((I.Nil, _), ModeSyn.Mnil), Adepth -> Adepth
          | ((I.SClo (S, s'), s), M), Adepth ->
              collectModeW' (((S, I.comp (s', s)), M), Adepth)
          | ((I.App (U, S), s), ModeSyn.Mapp (m, mS)), Adepth ->
              collectModeW'
                ( ((S, s), mS),
                  if modeEq (m, modeIn) then
                    collectExp (lG0, G, (U, s), modeRec, Adepth)
                  else Adepth )
        in
        let mS = valOf (ModeTable.modeLookup cid) in
        collectModeW' (((S, s), mS), Adepth)
    | lG0, G, modeIn, modeRec, (I.Pi ((D, P), V), s), Adepth ->
        raise
          (Error
             "Implementation restricted to the Horn fragment of the meta logic")
  (* collectG (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for_sml the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)

  let rec collectG (lG0, G, Vs, Adepth) =
    collectGW (lG0, G, Whnf.whnf Vs, Adepth)

  and collectGW (lG0, G, Vs, Adepth) =
    collectModeW
      (lG0, G, M.Bot, M.Top, Vs, collectModeW (lG0, G, M.Top, M.Bot, Vs, Adepth))
  (* collectDTop (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for_sml the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)

  let rec collectDTop (lG0, G, Vs, Adepth) =
    collectDTopW (lG0, G, Whnf.whnf Vs, Adepth)

  and collectDTopW = function
    | lG0, G, (I.Pi ((D, I.No), V2), s), Adepth ->
        collectG
          ( lG0,
            G,
            (V1, s),
            collectDTop
              (lG0, I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s), Adepth) )
    | lG0, G, Vs, Adepth -> collectModeW (lG0, G, M.Top, M.Top, Vs, Adepth)
  (* collectDBot (lG0, G, (V, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for_sml the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)

  let rec collectDBot (lG0, G, Vs, Adepth) =
    collectDBotW (lG0, G, Whnf.whnf Vs, Adepth)

  and collectDBotW = function
    | lG0, G, (I.Pi ((D, _), V), s), Adepth ->
        collectDBot (lG0, I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), Adepth)
    | lG0, G, Vs, Adepth -> collectModeW (lG0, G, M.Bot, M.Bot, Vs, Adepth)
  (* collect ((G,_,_), V) = A'
       collects EVar's and BVar's in V mode dependency order.

       Invariant:
       If   G  |- s : G'  and   G' |- V : L
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)

  let rec collect (M.Prefix (G, M, B), V) =
    let lG0 = I.ctxLength G in
    let A, k =
      collectDBot
        (lG0, G, (V, I.id), collectDTop (lG0, G, (V, I.id), (I.Null, lG0)))
    in
    A
  (*------------------------------------------------------------*)

  (* Second section: Abstracting over EVars and BVars that have *)

  (* been collected in mode dependency order                    *)

  (*------------------------------------------------------------*)

  (* lookupEV (A, r) = (k', V')

       Invariant:

       If   A ||- V
       and  G |- X : V' occuring in V
       then G x A |- k : V'
       and  . |- V' : type
    *)

  let rec lookupEV (A, r) =
    (* lookupEV' I.Null cannot occur by invariant *)
    let rec lookupEV' = function
      | I.Decl (A, EV (r, V, _)), r', k ->
          if r = r' then (k, V) else lookupEV' (A, r', k + 1)
      | I.Decl (A, BV), r', k -> lookupEV' (A, r', k + 1)
    in
    lookupEV' (A, r, 1)
  (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)

  let rec lookupBV (A, i) =
    (* lookupBV' I.Null cannot occur by invariant *)
    let rec lookupBV' = function
      | I.Decl (A, EV (r, V, _)), i, k -> lookupBV' (A, i, k + 1)
      | I.Decl (A, BV), 1, k -> k
      | I.Decl (A, BV), i, k -> lookupBV' (A, i - 1, k + 1)
    in
    lookupBV' (A, i, 1)
  (* abstractExpW (A, G, depth, (U, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- U : V    (U,s) in whnf
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  A ||- V
       then  G0 x A, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)

  let rec abstractExpW = function
    | A, G, depth, (V, s) -> V
    | A, G, depth, (I.Pi ((D, P), V), s) ->
        Abstract.piDepend
          ( (abstractDec (A, G, depth, (D, s)), P),
            abstractExp
              (A, I.Decl (G, I.decSub (D, s)), depth + 1, (V, I.dot1 s)) )
    | A, G, depth, (I.Lam (D, U), s) ->
        I.Lam
          ( abstractDec (A, G, depth, (D, s)),
            abstractExp
              (A, I.Decl (G, I.decSub (D, s)), depth + 1, (U, I.dot1 s)) )
    | A, G, depth, (I.Root (C, S), s) ->
        if k > depth then
          let k' = lookupBV (A, k - depth) in
          I.Root (I.BVar (k' + depth), abstractSpine (A, G, depth, (S, s)))
        else I.Root (C, abstractSpine (A, G, depth, (S, s)))
    | A, G, depth, (I.Root (C, S), s) ->
        I.Root (C, abstractSpine (A, G, depth, (S, s)))
    | A, G, depth, (I.EVar (r, _, V, _), s) ->
        (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *)
        let k, Vraised = lookupEV (A, r) in
        I.Root
          ( I.BVar (k + depth),
            abstractSub (A, G, depth, (Vraised, I.id), s, I.targetFam V, I.Nil)
          )
    | A, G, depth, (I.FgnExp csfe, s) ->
        I.FgnExpStd.Map.apply csfe (fun U -> abstractExp (A, G, depth, (U, s)))

  and abstractExp (A, G, depth, Us) = abstractExpW (A, G, depth, Whnf.whnf Us)

  and abstractSpine = function
    | A, G, depth, (I.Nil, _) -> I.Nil
    | A, G, depth, (I.App (U, S), s) ->
        I.App
          ( abstractExp (A, G, depth, (U, s)),
            abstractSpine (A, G, depth, (S, s)) )
    | A, G, depth, (I.SClo (S, s'), s) ->
        abstractSpine (A, G, depth, (S, I.comp (s', s)))

  and abstractSub (A, G, depth, XVt, s, b, S) =
    abstractSubW (A, G, depth, Whnf.whnf XVt, s, b, S)

  and abstractSubW = function
    | A, G, depth, (I.Root _, _), s, b, S -> S
    | A, G, depth, XVt, I.Shift k, b, S ->
        abstractSub
          (A, G, depth, XVt, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), b, S)
    | A, G, depth, XVt, I.Dot (I.Idx k, s), b, S ->
        let (I.Dec (x, V)) = I.ctxDec (G, k) in
        if k > depth then
          let k' = lookupBV (A, k - depth) in
          abstractSub
            ( A,
              G,
              depth,
              (XV', I.dot1 t),
              s,
              b,
              I.App (I.Root (I.BVar (k' + depth), I.Nil), S) )
        else
          abstractSub
            ( A,
              G,
              depth,
              (XV', I.dot1 t),
              s,
              b,
              I.App (I.Root (I.BVar k, I.Nil), S) )
    | A, G, depth, XVt, I.Dot (I.Exp U, s), b, S ->
        abstractSub
          ( A,
            G,
            depth,
            (XV', I.dot1 t),
            s,
            b,
            I.App (abstractExp (A, G, depth, (U, I.id)), S) )

  and abstractDec (A, G, depth, (I.Dec (xOpt, V), s)) =
    I.Dec (xOpt, abstractExp (A, G, depth, (V, s)))
  (* abstractCtx (A, (G, M)) = ((G', M') , G'')

       Let E be a list of EVars possibly occuring in G

       Invariant:
       G' = G x A
       M' = M x A    (similar to G x A, but just represents mode information)
       G'' = G [x] A
    *)

  let rec abstractCtx = function
    | I.Null, GM -> (GM, I.Null)
    | I.Decl (A, BV), M.Prefix (I.Decl (G, D), I.Decl (M, marg), I.Decl (B, b))
      ->
        let M.Prefix (G', M', B'), lG' = abstractCtx (A, M.Prefix (G, M, B)) in
        let D' = abstractDec (A, G, 0, (D, I.id)) in
        let (I.Dec (_, V)) = D' in
        let _ =
          if !Global.doubleCheck then typecheck (M.Prefix (G', M', B'), V)
          else ()
        in
        ( M.Prefix
            ( I.Decl (G', Names.decName (G', D')),
              I.Decl (M', marg),
              I.Decl (B', b) ),
          I.Decl (lG', D') )
    | I.Decl (A, EV (r, V, m)), GM ->
        let M.Prefix (G', M', B'), lG' = abstractCtx (A, GM) in
        let V'' = abstractExp (A, lG', 0, (V, I.id)) in
        let _ =
          if !Global.doubleCheck then typecheck (M.Prefix (G', M', B'), V'')
          else ()
        in
        ( M.Prefix
            ( I.Decl (G', Names.decName (G', I.Dec (None, V''))),
              I.Decl (M', m),
              I.Decl
                (B', match m with M.Top -> !MetaGlobal.maxSplit | M.Bot -> 0) ),
          lG' )
  (* abstract ((G, M), V) = ((G', M') , V')

       Invariant:
       If    G |- V : type    (M modes associated with G)
       then  G' |- V' : type  (M' modes associated with G')
       and   . ||- V'
    *)

  let rec abstract S =
    let _ = Names.varReset I.Null in
    let A = collect (GM, V) in
    let GM', _ = abstractCtx (A, GM) in
    let V' = abstractExp (A, G, 0, (V, I.id)) in
    let S = M.State (name, GM', V') in
    let _ = if !Global.doubleCheck then typecheck (GM', V') else () in
    S

  let abstract = abstract
  (* local *)
end

(* functor MetaAbstract *)
(* Meta Abstraction *)

(* Author: Carsten Schuermann *)

module type METAABSTRACT = sig
  module MetaSyn : METASYN

  exception Error of string

  val abstract : MetaSyn.state -> MetaSyn.state
end

(* signature METAABSTRACT *)
