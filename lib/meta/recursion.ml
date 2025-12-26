open Basis ;; 
(* Recursion: Version 1.3 *)

(* Author: Carsten Schuermann *)

module type MTPRECURSION = sig
  module StateSyn : Statesyn.State.STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.state -> operator
  val apply : operator -> StateSyn.state
  val menu : operator -> string
end

(* signature MTPRECURSION *)
(* Meta Recursion Version 1.3 *)

(* Author: Carsten Schuermann *)

(* See [Rohwedder,Pfenning ESOP'96] *)

module MTPRecursion
    (MTPGlobal : Global.MTPGLOBAL)
    (Global : Global.GLOBAL)
    (StateSyn' : Statesyn.State.STATESYN)
    (Abstract : Abstract.ABSTRACT)
    (MTPAbstract : Abstract.MTPABSTRACT)
    (FunTypeCheck : Funtypecheck.FUNTYPECHECK)
    (MTPrint : Mtprint.MTPRINT)
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY)
    (Conv : Conv.CONV)
    (Names : Names.NAMES)
    (Subordinate : Subordinate.SUBORDINATE)
    (Print : Print.PRINT)
    (TypeCheck : Typecheck.TYPECHECK)
    (Formatter : Formatter.FORMATTER)
    (FunPrint : Funprint.FUNPRINT) : MTPRECURSION = struct
  module StateSyn = StateSyn'

  exception Error of string

  type operator = StateSyn.state

  module I = IntSyn
  module F = FunSyn
  module S = StateSyn
  module N = Names
  module Fmt = Formatter
  module A = MTPAbstract

  type dec = Lemma of int * F.for_sml
  (* Residual Lemma *)

  let rec closedCtx = function
    | I.Null -> ()
    | I.Decl (G, D) ->
        if Abstract.closedDec (G, (D, I.id)) then raise Domain else closedCtx G
  (*  spine n = S'

        Invariant:
        S' = n;..;1;Nil
     *)

  let rec spine = function
    | 0 -> I.Nil
    | n -> I.App (I.Root (I.BVar n, I.Nil), spine (n - 1))
  (* someEVars (G, G1, s) = s'

       Invariant:
       If  |- G ctx
       and  G |- s : G
       then G |- s' : G, G1
    *)

  let rec someEVars = function
    | G, [], s -> s
    | G, I.Dec (_, V) :: L, s ->
        someEVars (G, L, I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s))
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx

       NOTE, should go into a different module. Code duplication!
    *)

  let rec ctxSub = function
    | [], s -> []
    | D :: G, s -> I.decSub (D, s) :: ctxSub (G, I.dot1 s)
  (* appendCtx ((G1, B1), T, G2) = (G', B')

       Invariant:
       If   |- G1 ctx
       and  G1 |- B1 tags
       and  T tag
       and  G1 |- G2 ctx
       then |- G' = G1, G2 ctx
       and  G' |- B' tags
    *)

  let rec appendCtx = function
    | GB1, T, [] -> GB1
    | (G1, B1), T, D :: G2 -> appendCtx ((I.Decl (G1, D), I.Decl (B1, T)), T, G2)
  (* createCtx ((G, B), ll, s) = ((G', B'), s', af')

     Invariant:
     If   |- G ctx
     and  G |- B tags
     and  . |- label list
     and  |- G1 ctx
     and  G |- s : G1

     then |- G' : ctx
     and  G' |- B' tags
     and  G' = G, G''
     and  G' |- s' : G1
     and  af : forall . |- AF aux formulas. Ex . |- AF' = {{G''}} AF  auxFor
     *)

  let rec createCtx = function
    | (G, B), [], s -> ((G, B), s, fun AF -> AF)
    | (G, B), n :: ll, s ->
        (* G |- s' : G1 *)
        (* G |- G2' ctx *)
        (* . |- G' = G, G2' ctx *)
        (* G' |- s'' : G0 *)
        let (F.LabelDec (l, G1, G2)) = F.labelLookup n in
        let t = someEVars (G, G1, I.id) in
        let G2' = ctxSub (G2, t) in
        let G', B' = appendCtx ((G, B), S.Parameter (Some n), G2') in
        let s' = I.comp (s, I.Shift (List.length G2')) in
        let GB'', s'', af'' = createCtx ((G', B'), ll, s') in
        (GB'', s'', fun AF -> A.Block ((G, t, List.length G1, G2'), af'' AF))
  (* createEVars' (G, G0) = s'

       Invariant :
       If   |- G ctx
       and  |- G0 ctx
       then G |- s' : G0
       and  s' = X1 .. Xn where n = |G0|
    *)

  let rec createEVars = function
    | G, I.Null -> I.Shift (I.ctxLength G)
    | G, I.Decl (G0, I.Dec (_, V)) ->
        let s = createEVars (G, G0) in
        I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s)
  (* checkCtx (G, G2, (V, s)) = B'

       Invariant:
       If   |- G = G0, G1 ctx
       and  G |- G2 ctx
       and  G |- s : G0
       and  G0 |- V : L
       then B' holds iff
            G1 = V1 .. Vn and G, G1, V1 .. Vi-1 |- Vi unifies with V [s o ^i] : L
    *)

  let rec checkCtx = function
    | G, [], (V2, s) -> false
    | G, D :: G2, (V2, s) ->
        Cs.CSManager.trail (fun () -> Unify.unifiable (G, (V1, I.id), (V2, s)))
        || checkCtx (I.Decl (G, D), G2, (V2, I.comp (s, I.shift)))
  (* checkLabels ((G', B'), V, ll, l) = lopt'

       Invariant:
       If   |- G' ctx
       and  G' |- B' ctx
       and  G' |- s : G0
       and  G0 |- V : type
       and  . |- ll label list
       and  . |- l label number
       then lopt' = NONE if no context block is applicable
       or   lopt' = SOME l' if context block l' is applicable

       NOTE: For this implementation we only pick the first applicable contextblock.
       It is not yet clear what should happen if there are inductive calls where more
       then one contextblocks are introduced --cs
    *)

  let rec checkLabels ((G', B'), (V, s), ll (* as nil *), l) =
    if l < 0 then None
    else
      (* G' |- t : G1 *)
      (* G |- G2' ctx *)
      let (F.LabelDec (name, G1, G2)) = F.labelLookup l in
      let s = someEVars (G', G1, I.id) in
      let G2' = ctxSub (G2, s) in
      let t = someEVars (G', G1, I.id) in
      let G2' = ctxSub (G2, t) in
      if (not (List.exists (fun l' -> l = l') ll)) && checkCtx (G', G2', (V, s))
      then Some l
      else checkLabels ((G', B'), (V, s), ll, l - 1)
  (*      | checkLabels _ = NONE  (* more than one context block is introduced *) *)

  (* appendRL (Ds1, Ds2) = Ds'

       Invariant:
       Ds1, Ds2 are a list of residual lemmas
       Ds' = Ds1 @ Ds2, where all duplicates are removed
    *)

  let rec appendRL = function
    | [], Ds -> Ds
    | L :: Ds1, Ds2 ->
        let Ds' = appendRL (Ds1, Ds2) in
        if
          List.exists
            (fun (Lemma (n', F')) ->
              n = n' && F.convFor ((F, I.id), (F', I.id)))
            Ds'
        then Ds'
        else L :: Ds'
  (* recursion ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) = Ds

       Invariant:

       If

       nih  is the id or the induction hypothesis
       |- Gall ctx
       Gall |- Fex : for_sml        (Fex doesn't contain any universal quantifiers)
       Gall |- Oex : order

       and
       ncurrent is the id of the current proof goal
       |- G0 ctx
       G0 |- B0 tags
       . |- ll label list
       G0 |- Ocurrent order
       G0 |- H history
       G0 |- F formula

       then
       G0 |- Ds decs
    *)

  let rec recursion
      ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), ll, Ocurrent, H, F)) =
    (* G' |- s' : G0 *)
    (* G' |- t' : Gall *)
    let (G', B'), s', af = createCtx ((G0, B0), ll, I.id) in
    let t' = createEVars (G', Gall) in
    let AF = af (A.Head (G', (Fex, t'), I.ctxLength Gall)) in
    let Oex' = S.orderSub (Oex, t') in
    let Ocurrent' = S.orderSub (Ocurrent, s') in
    let rec sc Ds =
      let Fnew = A.abstractApproxFor AF in
      if
        List.exists
          (fun nhist Fhist ->
            nih = nhist && F.convFor ((Fnew, I.id), (Fhist, I.id)))
          H
      then Ds
      else Lemma (nih, Fnew) :: Ds
    in
    let rec ac ((G', B'), Vs, Ds) =
      match checkLabels ((G', B'), Vs, ll, F.labelSize () - 1) with
      | None -> Ds
      | Some l' ->
          let Ds' =
            recursion
              ( (nih, Gall, Fex, Oex),
                (ncurrent, (G0, B0), l' :: ll, Ocurrent, H, F) )
          in
          appendRL (Ds', Ds)
    in
    if ncurrent < nih then ordle ((G', B'), Oex', Ocurrent', sc, ac, [])
    else ordlt ((G', B'), Oex', Ocurrent', sc, ac, [])

  and set_parameter (GB, X, k, sc, ac, Ds) =
    (* set_parameter' ((G, B), k, Ds) = Ds'

           Invariant:
           If    G1, D < G
        *)
    let rec set_parameter' = function
      | (I.Null, I.Null), _, Ds -> Ds
      | (I.Decl (G, D), I.Decl (B, S.Parameter _)), k, Ds ->
          let D' = I.decSub (D, I.Shift k) in
          let Ds' =
            Cs.CSManager.trail (fun () ->
                if
                  Unify.unifiable (G1, (V, I.id), (V', I.id))
                  && Unify.unifiable
                       (G1, (X, I.id), (I.Root (I.BVar k, I.Nil), I.id))
                then sc Ds
                else Ds)
          in
          set_parameter' ((G, B), k + 1, Ds')
      | (I.Decl (G, D), I.Decl (B, _)), k, Ds ->
          set_parameter' ((G, B), k + 1, Ds)
    in
    set_parameter' (GB, 1, Ds)

  and ltinit (GB, k, (Us, Vs), UsVs', sc, ac, Ds) =
    ltinitW (GB, k, Whnf.whnfEta (Us, Vs), UsVs', sc, ac, Ds)

  and ltinitW = function
    | GB, k, (Us, Vs), UsVs', sc, ac, Ds ->
        lt (GB, k, (Us, Vs), UsVs', sc, ac, Ds)
    | ( (G, B),
        k,
        ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)),
        ((U', s1'), (V', s2')),
        sc,
        ac,
        Ds ) ->
        ltinit
          ( ( I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)),
              I.Decl (B, S.Parameter None) ),
            k + 1,
            ((U, I.dot1 s1), (V, I.dot1 s2)),
            ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))),
            sc,
            ac,
            Ds )

  and lt (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) =
    ltW (GB, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ac, Ds)

  and ltW = function
    | GB, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, ac, Ds ->
        ltSpine (GB, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, ac, Ds)
    | GB, k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, ac, Ds -> (
        match I.ctxLookup (B, n) with
        | S.Parameter _ ->
            let (I.Dec (_, V')) = I.ctxDec (G, n) in
            ltSpine (GB, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ac, Ds)
        | S.Lemma _ -> Ds)
    | GB, _, _, ((I.EVar _, _), _), _, _, Ds -> Ds
    | ( GB,
        k,
        ((U, s1), (V, s2)),
        ((I.Lam (D, U'), s1'), (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
        sc,
        ac,
        Ds ) ->
        (* ctxBlock (GB, I.EClo (V1', s1'), k, sc, ac, Ds) *)
        let Ds' = Ds in
        if
          Subordinate.equiv (I.targetFam V, I.targetFam V1')
          (* == I.targetFam V2' *)
        then
          (* enforce that X gets only bound to parameters *)
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' = fun Ds'' -> set_parameter (GB, X, k, sc, ac, Ds'') in
          lt
            ( GB,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc',
              ac,
              Ds' )
        else if Subordinate.below (I.targetFam V1', I.targetFam V) then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          lt
            ( GB,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc,
              ac,
              Ds' )
        else Ds'

  and ltSpine (GB, k, (Us, Vs), (Ss', Vs'), sc, ac, Ds) =
    ltSpineW (GB, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, ac, Ds)

  and ltSpineW = function
    | GB, k, (Us, Vs), ((I.Nil, _), _), _, _, Ds -> Ds
    | GB, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, ac, Ds ->
        ltSpineW (GB, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, ac, Ds)
    | ( GB,
        k,
        (Us, Vs),
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        sc,
        ac,
        Ds ) ->
        let Ds' = le (GB, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ac, Ds) in
        ltSpine
          ( GB,
            k,
            (Us, Vs),
            ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
            sc,
            ac,
            Ds' )

  and eq ((G, B), (Us, Vs), (Us', Vs'), sc, ac, Ds) =
    Cs.CSManager.trail (fun () ->
        if Unify.unifiable (G, Vs, Vs') && Unify.unifiable (G, Us, Us') then
          sc Ds
        else Ds)

  and le (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds) =
    let Ds' = eq (GB, (Us, Vs), (Us', Vs'), sc, ac, Ds) in
    leW (GB, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ac, Ds')

  and leW = function
    | ( GB,
        k,
        ((U, s1), (V, s2)),
        ((I.Lam (D, U'), s1'), (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
        sc,
        ac,
        Ds ) ->
        let Ds' = ac (GB, (V1', s1'), Ds) in
        if
          Subordinate.equiv (I.targetFam V, I.targetFam V1')
          (* == I.targetFam V2' *)
        then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          (* enforces that X can only bound to parameter *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' = fun Ds'' -> set_parameter (GB, X, k, sc, ac, Ds'') in
          le
            ( GB,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc',
              ac,
              Ds' )
        else if Subordinate.below (I.targetFam V1', I.targetFam V) then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          (*              val sc'' = fn Ds'' => set_parameter (GB, X, k, sc, ac, Ds'')   (* BUG -cs *)
                val Ds''' =  le (GB, k, ((U, s1), (V, s2)),
                                 ((U', I.Dot (I.Exp (X), s1')),
                                  (V', I.Dot (I.Exp (X), s2'))), sc'', ac, Ds'') *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' = sc in
          let Ds'' =
            le
              ( GB,
                k,
                ((U, s1), (V, s2)),
                ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
                sc',
                ac,
                Ds' )
          in
          Ds''
        else Ds'
    | GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds ->
        lt (GB, k, (Us, Vs), (Us', Vs'), sc, ac, Ds)

  and ordlt = function
    | GB, S.Arg UsVs, S.Arg UsVs', sc, ac, Ds ->
        ltinit (GB, 0, UsVs, UsVs', sc, ac, Ds)
    | GB, S.Lex L, S.Lex L', sc, ac, Ds -> ordltLex (GB, L, L', sc, ac, Ds)
    | GB, S.Simul L, S.Simul L', sc, ac, Ds -> ordltSimul (GB, L, L', sc, ac, Ds)

  and ordltLex = function
    | GB, [], [], sc, ac, Ds -> Ds
    | GB, O :: L, O' :: L', sc, ac, Ds ->
        let Ds' =
          Cs.CSManager.trail (fun () -> ordlt (GB, O, O', sc, ac, Ds))
        in
        ordeq
          (GB, O, O', fun Ds'' -> (ordltLex (GB, L, L', sc, ac, Ds''), ac, Ds'))

  and ordltSimul = function
    | GB, [], [], sc, ac, Ds -> Ds
    | GB, O :: L, O' :: L', sc, ac, Ds ->
        let Ds'' =
          Cs.CSManager.trail (fun () ->
              ordlt
                ( GB,
                  O,
                  O',
                  fun Ds' -> (ordleSimul (GB, L, L', sc, ac, Ds'), ac, Ds) ))
        in
        ordeq
          (GB, O, O', fun Ds' -> (ordltSimul (GB, L, L', sc, ac, Ds'), ac, Ds''))

  and ordleSimul = function
    | GB, [], [], sc, ac, Ds -> sc Ds
    | GB, O :: L, O' :: L', sc, ac, Ds ->
        ordle
          (GB, O, O', fun Ds' -> (ordleSimul (GB, L, L', sc, ac, Ds'), ac, Ds))

  and ordeq = function
    | (G, B), S.Arg (Us, Vs), S.Arg (Us', Vs'), sc, ac, Ds ->
        if Unify.unifiable (G, Vs, Vs') && Unify.unifiable (G, Us, Us') then
          sc Ds
        else Ds
    | GB, S.Lex L, S.Lex L', sc, ac, Ds -> ordeqs (GB, L, L', sc, ac, Ds)
    | GB, S.Simul L, S.Simul L', sc, ac, Ds -> ordeqs (GB, L, L', sc, ac, Ds)

  and ordeqs = function
    | GB, [], [], sc, ac, Ds -> sc Ds
    | GB, O :: L, O' :: L', sc, ac, Ds ->
        ordeq (GB, O, O', fun Ds' -> (ordeqs (GB, L, L', sc, ac, Ds'), ac, Ds))

  and ordle (GB, O, O', sc, ac, Ds) =
    let Ds' = Cs.CSManager.trail (fun () -> ordeq (GB, O, O', sc, ac, Ds)) in
    ordlt (GB, O, O', sc, ac, Ds')
  (* skolem (n, (du, de), GB, w, F, sc) = (GB', s')

       Invariant:
       If   GB, Ds |- w : GB
       and  GB, G |- F formula
       and  du = #universal quantifiers in F
       and  de = #existential quantifiers in F
       and  sc is a continuation which
            for_sml all GB, Ds |- s' : GB
            returns s''  of type  GB, Ds, G'[...] |- w'' : GB, G
            and     V''  mapping (GB, Ds, G'[...] |- V  type)  to (GB, Ds |- {G'[...]} V type)
            and     F''  mapping (GB, Ds, G'[...] |- F) to (GB, Ds |- {{G'[...]}} F formula)
       then GB' = GB, Ds'
       and  |Ds'| = de
       and  each declaration in Ds' corresponds to one existential quantifier in F
       and  GB' |- s' : GB
    *)

  let rec skolem = function
    | (du, de), GB, w, F.True, sc -> (GB, w)
    | (du, de), GB, w, F.All (F.Prim D, F), sc ->
        skolem
          ( (du + 1, de),
            GB,
            w,
            F,
            fun s de' ->
              (* s'  :  GB, Ds |- s : GB   *)
              (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
              (* V'  : maps (GB, Ds, G'[...] |- V type) to (GB, Ds |- {G'[...]} V type) *)
              (* F'  : maps (GB, Ds, G'[...] |- F for_sml) to (GB, Ds |- {{G'[...]}} F for_sml) *)
              let s', V', F' = sc (s, de') in
              ( I.dot1 s' (* _   : GB, Ds, G'[...], D[?] |- _ : GB, G, D *),
                fun V ->
                  ( V'
                      (Abstract.piDepend
                         ( (Whnf.normalizeDec (D, s'), I.Meta),
                           Whnf.normalize (V, I.id) ))
                    (* _   : maps (GB, Ds, G'[....], D[?] |- V : type) to  (GB, Ds, |- {G[....], D[?]} V : type) *),
                    fun F -> F' (F.All (F.Prim (I.decSub (D, s')), F)) )
                (* _   : maps (GB, Ds, G'[....], D[?] |- F : for_sml) to  (GB, Ds, |- {{G[....], D[?]}} F : for_sml) *)
              ) )
    | (du, de), (G, B), w, F.Ex (I.Dec (name, V), F), sc ->
        (* s'  : GB, Ds, G'[...] |- s' : GB, G *)
        (* V'  : maps  (GB, Ds, G'[...] |- V : type)   to   (GB, Ds |- {G'[...]} V : type) *)
        (* F'  : maps  (GB, Ds, G'[...] |- F : for_sml)    to   (GB, Ds |- {{G'[...]}} F : for_sml) *)
        (* V1  : GB, Ds, G'[...] |- V1 = V [s'] : type *)
        (* V2  : GB, Ds |- {G'[...]} V2 : type *)
        (* F1  : GB, Ds, G'[...] |- F1 : for_sml *)
        (* F2  : GB, Ds |- {{G'[...]}} F2 : for_sml *)
        (* D2  : GB, Ds |- D2 : type *)
        (* T2  : GB, Ds |- T2 : tag *)
        let s', V', F' = sc (w, de) in
        let V1 = I.EClo (V, s') in
        let V2 = Whnf.normalize (V' V1, I.id) in
        let F1 = F.Ex (I.Dec (name, V1), F.True) in
        let F2 = F' F1 in
        let _ =
          if !Global.doubleCheck then FunTypeCheck.isFor (G, F2) else ()
        in
        let D2 = I.Dec (None, V2) in
        let T2 =
          match F2 with
          | F.All _ -> S.Lemma S.RL
          | _ -> S.Lemma (S.Splits !MTPGlobal.maxSplit)
        in
        skolem
          ( (du, de + 1),
            (I.Decl (G, D2), I.Decl (B, T2)),
            I.comp (w, I.shift),
            F,
            fun s de' ->
              (* s   : GB, Ds, D2 |- s : GB *)
              (* s'  : GB, Ds, D2, G'[...] |- s' : GB, G *)
              (* V'  : maps (GB, Ds, D2, G'[...] |- V type) to (GB, Ds, D2 |- {G'[...]} V type) *)
              (* F'  : maps (GB, Ds, D2, G'[...] |- F for_sml) to (GB, Ds, D2 |- {{G'[...]}} F for_sml) *)
              let s', V', F' = sc (s, de') in
              ( I.Dot (I.Exp (I.Root (I.BVar (du + (de' - de)), spine du)), s')
                (* _ : GB, Ds, D2, G'[...] |- s'' : GB, G, D *),
                V',
                F' ) )
  (* updateState (S, (Ds, s))

       Invariant:
       G context
       G' |- S state
       G |- Ds new decs
       G' |- s : G
    *)

  let rec updateState = function
    | S, ([], s) -> S
    | S, (Lemma (n', Frl') :: L, s) ->
        let (G'', B''), s' =
          skolem
            ( (0, 0),
              (G, B),
              I.id,
              F.forSub (Frl', s),
              fun s' _ -> (s', fun V' -> (V', fun F' -> F')) )
        in
        let s'' = I.comp (s, s') in
        updateState
          ( S.State
              ( n,
                (G'', B''),
                (IH, OH),
                d,
                S.orderSub (O, s'),
                (n', F.forSub (Frl', s''))
                :: map (fun n' F' -> (n', F.forSub (F', s'))) H,
                F.forSub (F, s') ),
            (L, s'') )
  (* selectFormula (n, G, (G0, F, O), S) = S'

       Invariant:
       If   G |- s : G0  and  G0 |- F formula and  G0 |- O order
       and  S is a state
       then S' is the state with
       sc returns with all addition assumptions/residual lemmas for_sml a certain
       branch of the theorem.
    *)

  let rec selectFormula = function
    | n, (G0, F.All (F.Prim D, F), S.All (_, O)), S ->
        selectFormula (n, (I.Decl (G0, D), F, O), S)
    | n, (G0, F.And (F1, F2), S.And (O1, O2)), S ->
        let n', S' = selectFormula (n, (G0, F1, O1), S) in
        selectFormula (n, (G0, F2, O2), S')
    | nih, (Gall, Fex, Oex), S ->
        let Ds =
          recursion
            ((nih, Gall, Fex, Oex), (ncurrent, (G0, B0), [], Ocurrent, H, F))
        in
        (nih + 1, updateState (S, (Ds, I.id)))

  let rec expand S =
    let _ = if !Global.doubleCheck then FunTypeCheck.isState S else () in
    let _, S' = selectFormula (1, (I.Null, IH, OH), S) in
    S'

  let rec apply S =
    if !Global.doubleCheck then FunTypeCheck.isState S else ();
    S

  let rec menu _ =
    "Recursion (calculates ALL new assumptions & residual lemmas)"

  let rec handleExceptions f P = try f P with Order.Error s -> raise (Error s)
  let expand = handleExceptions expand
  let apply = apply
  let menu = menu
  (* local *)
end

(* functor MTPRecursion *)
