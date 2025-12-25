open Basis ;; 
(* Meta Theorem Prover abstraction : Version 1.3 *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module type MTPABSTRACT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure FunSyn : Funsyn.FUNSYN !*)
  module StateSyn : Statesyn.State.STATESYN

  exception Error of string

  type approxFor =
    | Head of IntSyn.dctx * (FunSyn.for_sml * IntSyn.sub) * int
    | Block of (IntSyn.dctx * IntSyn.sub * int * IntSyn.dec list) * approxFor

  (*  | (t, G2), AF *)
  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.sub
  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp

  val abstractSub :
    IntSyn.sub
    * StateSyn.tag IntSyn.ctx
    * (IntSyn.dctx * StateSyn.tag IntSyn.ctx)
    * IntSyn.sub
    * StateSyn.tag IntSyn.ctx ->
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub

  val abstractSub' :
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx)
    * IntSyn.sub
    * StateSyn.tag IntSyn.ctx ->
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub

  val abstractApproxFor : approxFor -> FunSyn.for_sml
end

(* signature MTPABSTRACT *)
(* Meta Theorem Prover abstraction : Version 1.3 *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module MTPAbstract
    (StateSyn' : Statesyn.State.STATESYN)
    (Whnf : Whnf.WHNF)
    (Constraints : Constraints.CONSTRAINTS)
    (Unify : Unify.UNIFY)
    (Subordinate : Subordinate.SUBORDINATE)
    (TypeCheck : Typecheck.TYPECHECK)
    (FunTypeCheck : FUNTYPECHECK)
    (Abstract : ABSTRACT) : MTPABSTRACT = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure FunSyn = FunSyn' !*)

  module StateSyn = StateSyn'

  exception Error of string

  type approxFor =
    | Head of IntSyn.dctx * (FunSyn.for_sml * IntSyn.sub) * int
    | Block of (IntSyn.dctx * IntSyn.sub * int * IntSyn.dec list) * approxFor
  (*      | (t, G2), AF *)

  module I = IntSyn
  module F = FunSyn
  module S = StateSyn
  module C = Constraints
  (* Intermediate Data Structure *)

  type eBVar =
    | EV of I.exp option ref * I.exp * S.tag * int
    | BV of I.dec * S.tag
  (*
       We write {{K}} for_sml the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for_sml the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
       for_sml spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)

  let rec checkEmpty = function
    | [] -> ()
    | cnstrL -> (
        match C.simplify cnstrL with
        | [] -> ()
        | _ -> raise (Error "Typing ambiguous -- unresolved constraints"))
  (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)

  let rec eqEVar = function
    | I.EVar (r1, _, _, _), EV (r2, _, _, _) -> r1 = r2
    | _, _ -> false
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)

  let rec exists P K =
    let rec exists' = function
      | I.Null -> false
      | I.Decl (K', Y) -> P Y || exists' K'
    in
    exists' K

  let rec or_ = function
    | I.Maybe, _ -> I.Maybe
    | _, I.Maybe -> I.Maybe
    | I.Meta, _ -> I.Meta
    | _, I.Meta -> I.Meta
    | I.No, I.No -> I.No
  (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place an argument to a Skonst
             DP = Meta    iff k occurs in U and arguments to Skonsts
    *)

  let rec occursInExp = function
    | k, I.Uni _ -> I.No
    | k, I.Pi (DP, V) -> or_ (occursInDecP (k, DP), occursInExp (k + 1, V))
    | k, I.Root (H, S) -> occursInHead (k, H, occursInSpine (k, S))
    | k, I.Lam (D, V) -> or_ (occursInDec (k, D), occursInExp (k + 1, V))

  and occursInHead = function
    | k, I.BVar k', DP -> if k = k' then I.Maybe else DP
    | k, I.Const _, DP -> DP
    | k, I.Def _, DP -> DP
    | k, I.Skonst _, I.No -> I.No
    | k, I.Skonst _, I.Meta -> I.Meta
    | k, I.Skonst _, I.Maybe -> I.Meta

  and occursInSpine = function
    | _, I.Nil -> I.No
    | k, I.App (U, S) -> or_ (occursInExp (k, U), occursInSpine (k, S))

  and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
  and occursInDecP (k, (D, _)) = occursInDec (k, D)
  (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)

  (* optimize to have fewer traversals? -cs *)

  (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)

  let rec piDepend = function
    | DPV -> I.Pi DPV
    | DPV -> I.Pi DPV
    | (D, I.Maybe), V -> I.Pi ((D, occursInExp (1, V)), V)
  (* weaken (depth,  G, a) = (w')
    *)

  let rec weaken = function
    | I.Null, a -> I.id
    | I.Decl (G', D), a ->
        let w' = weaken (G', a) in
        if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
        else I.comp (w', I.shift)
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)

  let rec raiseType = function
    | I.Null, V -> V
    | I.Decl (G, D), V -> raiseType (G, I.Pi ((D, I.Maybe), V))

  let rec restore = function
    | 0, Gp -> (Gp, I.Null)
    | n, I.Decl (G, D) ->
        let Gp', GX' = restore (n - 1, G) in
        (Gp', I.Decl (GX', D))

  let rec concat = function
    | Gp, I.Null -> Gp
    | Gp, I.Decl (G, D) -> I.Decl (concat (Gp, G), D)
  (* collectExpW (T, d, G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for_sml BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)

  (* Possible optimization: Calculate also the normal form of the term *)

  let rec collectExpW = function
    | T, d, G, (I.Uni L, s), K -> K
    | T, d, G, (I.Pi ((D, _), V), s), K ->
        collectExp
          ( T,
            d,
            I.Decl (G, I.decSub (D, s)),
            (V, I.dot1 s),
            collectDec (T, d, G, (D, s), K) )
    | T, d, G, (I.Root (_, S), s), K ->
        collectSpine (S.decrease T, d, G, (S, s), K)
    | T, d, G, (I.Lam (D, U), s), K ->
        collectExp
          ( T,
            d,
            I.Decl (G, I.decSub (D, s)),
            (U, I.dot1 s),
            collectDec (T, d, G, (D, s), K) )
    | T, d, G, (X, s), K ->
        if exists (eqEVar X) K then collectSub (T, d, G, s, K)
        else
          (* optimization possible for_sml d = 0 *)
          let Gp, GX = restore (I.ctxLength GdX - d, GdX) in
          let _ = checkEmpty !cnstrs in
          let w = weaken (GX, I.targetFam V) in
          let iw = Whnf.invert w in
          let GX' = Whnf.strengthen (iw, GX) in
          let X' = I.newEVar (concat (Gp, GX'), I.EClo (V, iw)) in
          let _ = Unify.instantiateEVar (r, I.EClo (X', w), []) in
          let V' = raiseType (GX', I.EClo (V, iw)) in
          collectSub
            ( T,
              d,
              G,
              I.comp (w, s),
              I.Decl (collectExp (T, d, Gp, (V', I.id), K), EV (r', V', T, d))
            )
    | T, d, G, (I.FgnExp csfe, s), K ->
        I.FgnExpStd.fold csfe
          (fun (U, K') -> collectExp (T, d, G, (U, s), K'))
          K

  and collectExp (T, d, G, Us, K) = collectExpW (T, d, G, Whnf.whnf Us, K)

  and collectSpine = function
    | T, d, G, (I.Nil, _), K -> K
    | T, d, G, (I.SClo (S, s'), s), K ->
        collectSpine (T, d, G, (S, I.comp (s', s)), K)
    | T, d, G, (I.App (U, S), s), K ->
        collectSpine (T, d, G, (S, s), collectExp (T, d, G, (U, s), K))

  and collectDec (T, d, G, (I.Dec (_, V), s), K) =
    collectExp (T, d, G, (V, s), K)

  and collectSub = function
    | T, d, G, I.Shift _, K -> K
    | T, d, G, I.Dot (I.Idx _, s), K -> collectSub (T, d, G, s, K)
    | T, d, G, I.Dot (I.Exp U, s), K ->
        collectSub (T, d, G, s, collectExp (T, d, G, (U, I.id), K))
  (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)

  let rec abstractEVar = function
    | I.Decl (K', EV (r', _, _, d)), depth, X ->
        if r = r' then (I.BVar (depth + 1), d)
        else abstractEVar (K', depth + 1, X)
    | I.Decl (K', BV _), depth, X -> abstractEVar (K', depth + 1, X)
  (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)

  let rec lookupBV (K, i) =
    (* lookupBV' I.Null cannot occur by invariant *)
    let rec lookupBV' = function
      | I.Decl (K, EV (r, V, _, _)), i, k -> lookupBV' (K, i, k + 1)
      | I.Decl (K, BV _), 1, k -> k
      | I.Decl (K, BV _), i, k -> lookupBV' (K, i - 1, k + 1)
    in
    lookupBV' (K, i, 1)
  (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)

  let rec abstractExpW = function
    | K, depth, (U, s) -> U
    | K, depth, (I.Pi ((D, P), V), s) ->
        piDepend
          ( (abstractDec (K, depth, (D, s)), P),
            abstractExp (K, depth + 1, (V, I.dot1 s)) )
    | K, depth, (I.Root (H, S), s) ->
        if k > depth then
          let k' = lookupBV (K, k - depth) in
          I.Root (I.BVar (k' + depth), abstractSpine (K, depth, (S, s)))
        else I.Root (H, abstractSpine (K, depth, (S, s)))
    | K, depth, (I.Root (H, S), s) ->
        I.Root (H, abstractSpine (K, depth, (S, s)))
    | K, depth, (I.Lam (D, U), s) ->
        I.Lam
          ( abstractDec (K, depth, (D, s)),
            abstractExp (K, depth + 1, (U, I.dot1 s)) )
    | K, depth, (X, s) ->
        let H, d = abstractEVar (K, depth, X) in
        I.Root (H, abstractSub (I.ctxLength G - d, K, depth, s, I.Nil))
    | K, depth, (I.FgnExp csfe, s) ->
        I.FgnExpStd.Map.apply csfe (fun U -> abstractExp (K, depth, (U, s)))

  and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

  and abstractSub = function
    | n, K, depth, I.Shift k, S ->
        if n > 0 then
          abstractSub (n, K, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), S)
        else (* n = 0 *)
          S
    | n, K, depth, I.Dot (I.Idx k, s), S ->
        let H =
          if k > depth then
            let k' = lookupBV (K, k - depth) in
            I.BVar (k' + depth)
          else I.BVar k
        in
        abstractSub (n - 1, K, depth, s, I.App (I.Root (H, I.Nil), S))
    | n, K, depth, I.Dot (I.Exp U, s), S ->
        abstractSub
          (n - 1, K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S))

  and abstractSpine = function
    | K, depth, (I.Nil, _) -> I.Nil
    | K, depth, (I.SClo (S, s'), s) ->
        abstractSpine (K, depth, (S, I.comp (s', s)))
    | K, depth, (I.App (U, S), s) ->
        I.App (abstractExp (K, depth, (U, s)), abstractSpine (K, depth, (S, s)))

  and abstractDec (K, depth, (I.Dec (x, V), s)) =
    I.Dec (x, abstractExp (K, depth, (V, s)))
  (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for_sml some L'
    *)

  let rec getLevel = function
    | I.Uni _ -> I.Kind
    | I.Pi (_, U) -> getLevel U
    | I.Root _ -> I.Type
    | I.Redex (U, _) -> getLevel U
    | I.Lam (_, U) -> getLevel U
    | I.EClo (U, _) -> getLevel U
  (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for_sml some L'
    *)

  let rec checkType V =
    match getLevel V with
    | I.Type -> ()
    | _ -> raise (Error "Typing ambiguous -- free type variable")
  (* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)

  let rec abstractCtx = function
    | I.Null -> (I.Null, I.Null)
    | I.Decl (K', EV (_, V', T, _)) ->
        let V'' = abstractExp (K', 0, (V', I.id)) in
        let _ = checkType V'' in
        let G', B' = abstractCtx K' in
        let D' = I.Dec (None, V'') in
        (I.Decl (G', D'), I.Decl (B', T))
    | I.Decl (K', EV (_, V', T, _)) ->
        let V'' = abstractExp (K', 0, (V', I.id)) in
        let _ = checkType V'' in
        let G', B' = abstractCtx K' in
        let D' = I.Dec (None, V'') in
        (I.Decl (G', D'), I.Decl (B', S.None))
    | I.Decl (K', BV (D, T)) ->
        let D' = abstractDec (K', 0, (D, I.id)) in
        let G', B' = abstractCtx K' in
        (I.Decl (G', D'), I.Decl (B', T))
  (* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)

  let rec abstractGlobalSub = function
    | K, I.Shift _, I.Null -> I.Shift (I.ctxLength K)
    | K, I.Shift n, B ->
        abstractGlobalSub (K, I.Dot (I.Idx (n + 1), I.Shift (n + 1)), B)
    | K, I.Dot (I.Idx k, s'), I.Decl (B, T) ->
        I.Dot (I.Idx (lookupBV (K, k)), abstractGlobalSub (K, s', B))
    | K, I.Dot (I.Exp U, s'), I.Decl (B, T) ->
        I.Dot
          (I.Exp (abstractExp (K, 0, (U, I.id))), abstractGlobalSub (K, s', B))
  (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)

  let rec collectGlobalSub = function
    | G0, I.Shift _, I.Null, collect -> collect
    | G0, s, B, collect ->
        let (F.LabelDec (name, _, G2)) = F.labelLookup l in
        skip (G0, List.length G2, s, B, collect)
    | G0, I.Dot (I.Exp U, s), I.Decl (B, T), collect ->
        collectGlobalSub
          ( G0,
            s,
            B,
            fun (d, K) -> collect (d, collectExp (T, d, G0, (U, I.id), K)) )

  and skip = function
    | G0, 0, s, B, collect -> collectGlobalSub (G0, s, B, collect)
    | I.Decl (G0, D), n, s, I.Decl (B, T), collect ->
        skip
          ( G0,
            n - 1,
            I.invDot1 s,
            B,
            fun (d, K) -> collect (d + 1, I.Decl (K, BV (D, T))) )
  (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)

  let rec abstractNew ((G0, B0), s, B) =
    let cf = collectGlobalSub (G0, s, B, fun (_, K') -> K') in
    let K = cf (0, I.Null) in
    (abstractCtx K, abstractGlobalSub (K, s, B))
  (* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)

  let rec abstractSubAll (t, B1, (G0, B0), s, B) =
    (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)
    let rec skip'' = function
      | K, (I.Null, I.Null) -> K
      | K, (I.Decl (G0, D), I.Decl (B0, T)) ->
          I.Decl (skip'' (K, (G0, B0)), BV (D, T))
    in
    let collect2 = collectGlobalSub (G0, s, B, fun (_, K') -> K') in
    let collect0 = collectGlobalSub (I.Null, t, B1, fun (_, K') -> K') in
    let K0 = collect0 (0, I.Null) in
    let K1 = skip'' (K0, (G0, B0)) in
    let d = I.ctxLength G0 in
    let K = collect2 (d, K1) in
    (abstractCtx K, abstractGlobalSub (K, s, B))
  (* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)

  let rec abstractFor = function
    | K, depth, (F.All (F.Prim D, F), s) ->
        F.All
          ( F.Prim (abstractDec (K, depth, (D, s))),
            abstractFor (K, depth + 1, (F, I.dot1 s)) )
    | K, depth, (F.Ex (D, F), s) ->
        F.Ex
          ( abstractDec (K, depth, (D, s)),
            abstractFor (K, depth + 1, (F, I.dot1 s)) )
    | K, depth, (F.True, s) -> F.True
    | K, depth, (F.And (F1, F2), s) ->
        F.And (abstractFor (K, depth, (F1, s)), abstractFor (K, depth, (F2, s)))
  (* abstract (Gx, F) = F'

       Invariant:
       If   G, Gx |- F formula
       then G |- F' = {{Gx}} F formula
    *)

  let rec allClo = function
    | I.Null, F -> F
    | I.Decl (Gx, D), F -> allClo (Gx, F.All (F.Prim D, F))

  let rec convert = function
    | I.Null -> I.Null
    | I.Decl (G, D) -> I.Decl (convert G, BV (D, S.Parameter None))

  let rec createEmptyB = function
    | 0 -> I.Null
    | n -> I.Decl (createEmptyB (n - 1), S.None)

  let rec lower = function
    | _, 0 -> I.Null
    | I.Decl (G, D), n -> I.Decl (lower (G, n - 1), D)

  let rec split = function
    | G, 0 -> (G, I.Null)
    | I.Decl (G, D), n ->
        let G1, G2 = split (G, n - 1) in
        (G1, I.Decl (G2, D))
  (* shift G = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, G ctx
       then G0, V, G |- s' : G0, G
    *)

  let rec shift = function
    | I.Null -> I.shift
    | I.Decl (G, _) -> I.dot1 (shift G)
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)

  let rec ctxSub = function
    | [], s -> []
    | D :: G, s -> I.decSub (D, s) :: ctxSub (G, I.dot1 s)
  (* weaken2 (G, a, i, S) = w'

       Invariant:
       G |- w' : Gw
       Gw < G
       G |- S : {Gw} V > V
    *)

  let rec weaken2 = function
    | I.Null, a, i -> (I.id, fun S -> S)
    | I.Decl (G', D), a, i ->
        let w', S' = weaken2 (G', a, i + 1) in
        if Subordinate.belowEq (I.targetFam V, a) then
          (I.dot1 w', fun S -> I.App (I.Root (I.BVar i, I.Nil), S))
        else (I.comp (w', I.shift), S')
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)

  let rec raiseType = function
    | I.Null, V -> V
    | I.Decl (G, D), V ->
        raiseType
          (G, Abstract.piDepend ((Whnf.normalizeDec (D, I.id), I.Maybe), V))
  (* raiseFor (G, F, w, sc) = F'

       Invariant:
       If   G0 |- G ctx
       and  G0, G, GF |- F for_sml
       and  G0, {G} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, G[..] |- s : G0, G, GF)
       then G0, {G} GF |- F' for_sml
    *)

  let rec raiseFor = function
    | k, Gorig, F, w, sc -> F
    | k, Gorig, F.Ex (I.Dec (name, V), F), w, sc ->
        (* G0, {G}GF[..], G |- s : G0, G, GF *)
        (* G0, {G}GF[..], G |- V' : type *)
        (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
        (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
        (* Generalize the invariant for_sml Whnf.strengthen --cs *)
        (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
        (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
        (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
        (* G0, {G}GF[..], G |- s : G0, G, GF *)
        let G = F.listToCtx (ctxSub (F.ctxToList Gorig, w)) in
        let g = I.ctxLength G in
        let s = sc (w, k) in
        let V' = I.EClo (V, s) in
        let nw, S = weaken2 (G, I.targetFam V, 1) in
        let iw = Whnf.invert nw in
        let Gw = Whnf.strengthen (iw, G) in
        let V'' = Whnf.normalize (V', iw) in
        let V''' = Whnf.normalize (raiseType (Gw, V''), I.id) in
        let S''' = S I.Nil in
        let sc' =
         fun (w', k') ->
          (* G0, GA |- w' : G0 *)
          (* G0, GA, G[..] |- s' : G0, G, GF *)
          let s' = sc (w', k') in
          I.Dot (I.Exp (I.Root (I.BVar (g + k' - k), S''')), s')
         (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
        in
        let F' = raiseFor (k + 1, Gorig, F, I.comp (w, I.shift), sc') in
        F.Ex (I.Dec (name, V'''), F')
    | k, Gorig, F.All (F.Prim (I.Dec (name, V)), F), w, sc ->
        (*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)
                  val V' = Whnf.normalize (raiseType (G, Whnf.normalize (V, s)), I.id)
                                        (* G0, {G}GF[..] |- V' = {G}(V[s]) : type *)
                  val S' = spine g
                                        (* G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] *)
                  val sc' = fn (w', k') =>
                              let
                                        (* G0, GA |- w' : G0 *)
                                val s' = sc (w', k')
                                        (* G0, GA, G[..] |- s' : G0, G, GF *)
                              in
                                I.Dot (I.Exp (I.Root (I.BVar (g + k'-k), S')), s')
                                        (* G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V *)
                              end
                  val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
                in
                  F.All (F.Prim (I.Dec (name, V')), F')
*)
        (* G0, {G}GF[..], G |- s : G0, G, GF *)
        (* G0, {G}GF[..], G |- V' : type *)
        (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)
        (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
        (* Generalize the invariant for_sml Whnf.strengthen --cs *)
        (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
        (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
        (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
        (* G0, {G}GF[..], G |- s : G0, G, GF *)
        let G = F.listToCtx (ctxSub (F.ctxToList Gorig, w)) in
        let g = I.ctxLength G in
        let s = sc (w, k) in
        let V' = I.EClo (V, s) in
        let nw, S = weaken2 (G, I.targetFam V, 1) in
        let iw = Whnf.invert nw in
        let Gw = Whnf.strengthen (iw, G) in
        let V'' = Whnf.normalize (V', iw) in
        let V''' = Whnf.normalize (raiseType (Gw, V''), I.id) in
        let S''' = S I.Nil in
        let sc' =
         fun (w', k') ->
          (* G0, GA |- w' : G0 *)
          (* G0, GA, G[..] |- s' : G0, G, GF *)
          let s' = sc (w', k') in
          I.Dot (I.Exp (I.Root (I.BVar (g + k' - k), S''')), s')
         (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
        in
        let F' = raiseFor (k + 1, Gorig, F, I.comp (w, I.shift), sc') in
        F.All (F.Prim (I.Dec (name, V''')), F')
  (* the other case of F.All (F.Block _, _) is not yet covered *)

  let rec extend = function
    | K, [] -> K
    | K, D :: L -> extend (I.Decl (K, BV (D, S.None)), L)
  (* makeFor (G, w, AF) = F'

       Invariant :
       If   |- G ctx
       and  G |- w : G'
       and  G' |- AF approx for_sml
       then G'; . |- F' = {EVARS} AF  for_sml
    *)

  let rec makeFor = function
    | K, w, Head (G, (F, s), d) ->
        (*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
        let cf = collectGlobalSub (G, s, createEmptyB d, fun (_, K') -> K') in
        let k = I.ctxLength K in
        let K' = cf (I.ctxLength G, K) in
        let k' = I.ctxLength K' in
        let GK, BK = abstractCtx K' in
        let _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx GK else () in
        let w' = I.comp (w, I.Shift (k' - k)) in
        let FK = abstractFor (K', 0, (F, s)) in
        let _ =
          if !Global.doubleCheck then FunTypeCheck.isFor (GK, FK) else ()
        in
        let GK1, GK2 = split (GK, k' - k) in
        (GK1, allClo (GK2, FK))
    | K, w, Block ((G, t, d, G2), AF) ->
        (* BUG *)
        let k = I.ctxLength K in
        let collect =
          collectGlobalSub (G, t, createEmptyB d, fun (_, K') -> K')
        in
        let K' = collect (I.ctxLength G, K) in
        let k' = I.ctxLength K' in
        let K'' = extend (K', G2) in
        let w' = F.dot1n (F.listToCtx G2, I.comp (w, I.Shift (k' - k))) in
        let GK, F' = makeFor (K'', w', AF) in
        let _ =
          if !Global.doubleCheck then FunTypeCheck.isFor (GK, F') else ()
        in
        let GK1, GK2 = split (GK, List.length G2) in
        let F'' = raiseFor (0, GK2, F', I.id, fun (w, _) -> F.dot1n (GK2, w)) in
        let _ =
          if !Global.doubleCheck then FunTypeCheck.isFor (GK1, F'') else ()
        in
        let GK11, GK12 = split (GK1, k' - k) in
        let F''' = allClo (GK12, F'') in
        let _ =
          if !Global.doubleCheck then FunTypeCheck.isFor (GK11, F''') else ()
        in
        (GK11, F''')

  let rec abstractApproxFor = function
    | AF ->
        let _, F = makeFor (convert G, I.id, AF) in
        F
    | AF ->
        let _, F = makeFor (convert G, I.id, AF) in
        F

  let weaken = weaken
  let raiseType = raiseType
  let abstractSub = abstractSubAll
  let abstractSub' = abstractNew
  let abstractApproxFor = abstractApproxFor
end

(* functor MTPAbstract *)
