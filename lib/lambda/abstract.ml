open Basis

(* Abstraction *)

(* Author: Frank Pfenning, Carsten Schuermann *)

module type ABSTRACT = sig
  exception Error of string

  val piDepend : (IntSyn.dec * IntSyn.depend) * IntSyn.exp -> IntSyn.exp
  val closedDec : IntSyn.dec IntSyn.ctx * (IntSyn.dec * IntSyn.sub) -> bool
  val closedSub : IntSyn.dec IntSyn.ctx * IntSyn.sub -> bool
  val closedExp : IntSyn.dec IntSyn.ctx * (IntSyn.exp * IntSyn.sub) -> bool
  val closedCtx : IntSyn.dec IntSyn.ctx -> bool
  val closedCTX : Tomega.dec IntSyn.ctx -> bool
  val abstractDecImp : IntSyn.exp -> int * IntSyn.exp
  val abstractDef : IntSyn.exp * IntSyn.exp -> int * (IntSyn.exp * IntSyn.exp)

  val abstractCtxs :
    IntSyn.dec IntSyn.ctx list ->
    IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx list

  val abstractTomegaSub : Tomega.sub -> Tomega.dec IntSyn.ctx * Tomega.sub
  val abstractTomegaPrg : Tomega.prg -> Tomega.dec IntSyn.ctx * Tomega.prg
  val abstractSpine : IntSyn.spine * IntSyn.sub -> IntSyn.dctx * IntSyn.spine

  val collectEVars :
    IntSyn.dctx * IntSyn.eclo * IntSyn.exp list -> IntSyn.exp list

  val collectEVarsSpine :
    IntSyn.dctx * (IntSyn.spine * IntSyn.sub) * IntSyn.exp list ->
    IntSyn.exp list

  val raiseTerm : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
end

(* signature ABSTRACT *)
(* Abstraction *)

(* Author: Frank Pfenning, Carsten Schuermann *)

(* Modified: Roberto Virga *)

module Abstract
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY)
    (Constraints : Constraints.CONSTRAINTS) : ABSTRACT = struct
  exception Error of string

  module I = IntSyn
  module T = Tomega
  module C = Constraints
  module O = Order
  (* Intermediate Data Structure *)

  type eFLVar =
    | EV of I.exp
    | FV of string * I.exp
    | LV of I.block
    | PV of T.prg
  (*     | P                            *)

  (*
       We write {{K}} for_sml the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for_sml the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for_sml spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

  (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)

  let rec collectConstraints = function
    | I.Null -> []
    | I.Decl (G, FV _) -> collectConstraints G
    | I.Decl (G, EV (I.EVar (_, _, _, { contents = [] }))) ->
        collectConstraints G
    | I.Decl (G, EV (I.EVar (_, _, _, { contents = cnstrL }))) ->
        C.simplify cnstrL @ collectConstraints G
    | I.Decl (G, LV _) -> collectConstraints G
  (* checkConstraints (K) = ()
       Effect: raises Constraints.Error(C) if K contains unresolved constraints
    *)

  let rec checkConstraints K =
    let constraints = collectConstraints K in
    let _ =
      match constraints with [] -> () | _ -> raise (C.Error constraints)
    in
    ()
  (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)

  (*
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error "Typing ambiguous -- unresolved constraints")
    *)

  (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)

  let rec eqEVar = function
    | I.EVar (r1, _, _, _), EV (I.EVar (r2, _, _, _)) -> r1 = r2
    | _, _ -> false
  (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)

  let rec eqFVar = function
    | I.FVar (n1, _, _), FV (n2, _) -> n1 = n2
    | _, _ -> false
  (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)

  let rec eqLVar = function
    | I.LVar (r1, _, _), LV (I.LVar (r2, _, _)) -> r1 = r2
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
  (* this should be non-strict *)

  (* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)

  (* Wed Aug  6 16:37:57 2003 -fp *)

  (* !!! *)

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
    | k, I.FgnExp csfe ->
        I.FgnExpStd.fold csfe
          (fun U DP -> or_ (DP, occursInExp (k, Whnf.normalize (U, I.id))))
          I.No

  and occursInHead = function
    | k, I.BVar k', DP -> if k = k' then I.Maybe else DP
    | k, I.Const _, DP -> DP
    | k, I.Def _, DP -> DP
    | k, I.Proj _, DP -> DP
    | k, I.FgnConst _, DP -> DP
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
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)

  let rec raiseType = function
    | I.Null, V -> V
    | I.Decl (G, D), V -> raiseType (G, I.Pi ((D, I.Maybe), V))
  (* raiseTerm (G, U) = [[G]] U

       Invariant:
       If G |- U : V
       then  . |- [[G]] U : {{G}} V

       All abstractions are potentially dependent.
    *)

  let rec raiseTerm = function
    | I.Null, U -> U
    | I.Decl (G, D), U -> raiseTerm (G, I.Lam (D, U))
  (* collectExpW (G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for_sml FVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and FVars in (U,s)
    *)

  (* Possible optimization: Calculate also the normal form of the term *)

  let rec collectExpW = function
    | G, (I.Uni L, s), K -> K
    | G, (I.Pi ((D, _), V), s), K ->
        collectExp
          (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (G, (D, s), K))
    | G, (I.Root (F, S), s), K ->
        if exists (eqFVar F) K then collectSpine (G, (S, s), K)
        else (* s' = ^|G| *)
          collectSpine
            (G, (S, s), I.Decl (collectExp (I.Null, (V, I.id), K), FV (name, V)))
    | G, (I.Root (I.Proj (L, i), S), s), K ->
        collectSpine (G, (S, s), collectBlock (G, I.blockSub (L, s), K))
    | G, (I.Root (_, S), s), K -> collectSpine (G, (S, s), K)
    | G, (I.Lam (D, U), s), K ->
        collectExp
          (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (G, (D, s), K))
    | G, (X, s), K ->
        if exists (eqEVar X) K then collectSub (G, s, K)
        else
          (* val _ = checkEmpty !cnstrs *)
          (* inefficient *)
          let V' = raiseType (GX, V) in
          let K' = collectExp (I.Null, (V', I.id), K) in
          collectSub (G, s, I.Decl (K', EV X))
    | G, (I.FgnExp csfe, s), K ->
        I.FgnExpStd.fold csfe (fun U K -> collectExp (G, (U, s), K)) K

  and collectExp (G, Us, K) = collectExpW (G, Whnf.whnf Us, K)

  and collectSpine = function
    | G, (I.Nil, _), K -> K
    | G, (I.SClo (S, s'), s), K -> collectSpine (G, (S, I.comp (s', s)), K)
    | G, (I.App (U, S), s), K ->
        collectSpine (G, (S, s), collectExp (G, (U, s), K))

  and collectDec = function
    | G, (I.Dec (_, V), s), K -> collectExp (G, (V, s), K)
    | G, (I.BDec (_, (_, t)), s), K -> collectSub (G, I.comp (t, s), K)
    | G, (I.NDec _, s), K -> K

  and collectSub = function
    | G, I.Shift _, K -> K
    | G, I.Dot (I.Idx _, s), K -> collectSub (G, s, K)
    | G, I.Dot (I.Exp U, s), K -> collectSub (G, s, collectExp (G, (U, I.id), K))
    | G, I.Dot (I.Block B, s), K -> collectSub (G, s, collectBlock (G, B, K))

  and collectBlock = function
    | G, I.LVar ({ contents = Some B }, sk, _), K ->
        collectBlock (G, I.blockSub (B, sk), K)
    | G, L, K ->
        if exists (eqLVar L) K then collectSub (G, I.comp (t, sk), K)
        else I.Decl (collectSub (G, I.comp (t, sk), K), LV L)
  (* was: t in the two lines above, July 22, 2010, -fp -cs *)

  (* | collectBlock (G, I.Bidx _, K) = K *)

  (* should be impossible: Fronts of substitutions are never Bidx *)

  (* Sat Dec  8 13:30:43 2001 -fp *)

  (* collectCtx (G0, G, K) = (G0', K')
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars and FVars in G
    *)

  let rec collectCtx = function
    | G0, I.Null, K -> (G0, K)
    | G0, I.Decl (G, D), K ->
        let G0', K' = collectCtx (G0, G, K) in
        let K'' = collectDec (G0', (D, I.id), K') in
        (I.Decl (G0, D), K'')
  (* collectCtxs (G0, Gs, K) = K'
       Invariant: G0 |- G1,...,Gn ctx where Gs = [G1,...,Gn]
       and K' = K, K'' where K'' contains all EVars and FVars in G1,...,Gn
    *)

  let rec collectCtxs = function
    | G0, [], K -> K
    | G0, G :: Gs, K ->
        let G0', K' = collectCtx (G0, G, K) in
        collectCtxs (G0', Gs, K')
  (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)

  let rec abstractEVar = function
    | I.Decl (K', EV (I.EVar (r', _, _, _))), depth, X ->
        if r = r' then I.BVar (depth + 1) else abstractEVar (K', depth + 1, X)
    | I.Decl (K', _), depth, X -> abstractEVar (K', depth + 1, X)
  (* abstractFVar (K, depth, F) = C'

       Invariant:
       If   G |- F : V
       and  |G| = depth
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)

  let rec abstractFVar = function
    | I.Decl (K', FV (n', _)), depth, F ->
        if n = n' then I.BVar (depth + 1) else abstractFVar (K', depth + 1, F)
    | I.Decl (K', _), depth, F -> abstractFVar (K', depth + 1, F)
  (* abstractLVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)

  let rec abstractLVar = function
    | I.Decl (K', LV (I.LVar (r', _, _))), depth, L ->
        if r = r' then I.Bidx (depth + 1) else abstractLVar (K', depth + 1, L)
    | I.Decl (K', _), depth, L -> abstractLVar (K', depth + 1, L)
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
    | K, depth, (I.Root (F, S), s) ->
        I.Root (abstractFVar (K, depth, F), abstractSpine (K, depth, (S, s)))
    | K, depth, (I.Root (I.Proj (L, i), S), s) ->
        I.Root
          ( I.Proj (abstractLVar (K, depth, L), i),
            abstractSpine (K, depth, (S, s)) )
    | K, depth, (I.Root (H, S), s) ->
        I.Root (H, abstractSpine (K, depth, (S, s)))
    | K, depth, (I.Lam (D, U), s) ->
        I.Lam
          ( abstractDec (K, depth, (D, s)),
            abstractExp (K, depth + 1, (U, I.dot1 s)) )
    | K, depth, (X, s) ->
        I.Root (abstractEVar (K, depth, X), abstractSub (K, depth, s, I.Nil))
    | K, depth, (I.FgnExp csfe, s) ->
        I.FgnExpStd.Map.apply csfe (fun U -> abstractExp (K, depth, (U, s)))

  and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

  and abstractSub = function
    | K, depth, I.Shift k, S ->
        if k < depth then
          abstractSub (K, depth, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), S)
        else (* k = depth *)
          S
    | K, depth, I.Dot (I.Idx k, s), S ->
        abstractSub (K, depth, s, I.App (I.Root (I.BVar k, I.Nil), S))
    | K, depth, I.Dot (I.Exp U, s), S ->
        abstractSub (K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S))

  and abstractSpine = function
    | K, depth, (I.Nil, _) -> I.Nil
    | K, depth, (I.SClo (S, s'), s) ->
        abstractSpine (K, depth, (S, I.comp (s', s)))
    | K, depth, (I.App (U, S), s) ->
        I.App (abstractExp (K, depth, (U, s)), abstractSpine (K, depth, (S, s)))

  and abstractDec (K, depth, (I.Dec (x, V), s)) =
    I.Dec (x, abstractExp (K, depth, (V, s)))
  (* abstractSOME (K, s) = s'
       s' = {{s}}_K

       Invariant:
       If    . |- s : Gsome
       and   K is internal context in dependency order
       and   K ||- s
       then  {{K}} |- s' : Gsome  --- not changing domain of s'

       Update: modified for_sml globality invariant of . |- t : Gsome
       Sat Dec  8 13:35:55 2001 -fp
       Above is now incorrect
       Sun Dec  1 22:36:50 2002 -fp
    *)

  let rec abstractSOME = function
    | K, I.Shift 0 -> I.Shift (I.ctxLength K)
    | K, I.Shift n -> I.Shift (I.ctxLength K)
    | K, I.Dot (I.Idx k, s) -> I.Dot (I.Idx k, abstractSOME (K, s))
    | K, I.Dot (I.Exp U, s) ->
        I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractSOME (K, s))
    | K, I.Dot (I.Block L, s) ->
        I.Dot (I.Block (abstractLVar (K, 0, L)), abstractSOME (K, s))
  (* I.Block (I.Bidx _) should be head of substitutions *)

  (* abstractCtx (K, depth, G) = (G', depth')
       where G' = {{G}}_K

       Invariants:
       If G0 |- G ctx
       and K ||- G
       and |G0| = depth
       then {{K}}, G0 |- G' ctx
       and . ||- G'
       and |G0,G| = depth'
    *)

  let rec abstractCtx = function
    | K, depth, I.Null -> (I.Null, depth)
    | K, depth, I.Decl (G, D) ->
        let G', depth' = abstractCtx (K, depth, G) in
        let D' = abstractDec (K, depth', (D, I.id)) in
        (I.Decl (G', D'), depth' + 1)
  (* abstractCtxlist (K, depth, [G1,...,Gn]) = [G1',...,Gn']
       where Gi' = {{Gi}}_K

       Invariants:
       if G0 |- G1,...,Gn ctx
       and K ||- G1,...,Gn
       and |G0| = depth
       then {{K}}, G0 |- G1',...,Gn' ctx
       and . ||- G1',...,Gn'
    *)

  let rec abstractCtxlist = function
    | K, depth, [] -> []
    | K, depth, G :: Gs ->
        let G', depth' = abstractCtx (K, depth, G) in
        let Gs' = abstractCtxlist (K, depth', Gs) in
        G' :: Gs'
  (* dead code under new reconstruction -kw
    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for_sml some L'
    *)
    fun getLevel (I.Uni _) = I.Kind
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for_sml some L'
    *)
    fun checkType V =
        (case getLevel V
           of I.Type => ()
            | _ => raise Error "Typing ambiguous -- free type variable")
    *)

  (* abstractKPi (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)

  let rec abstractKPi = function
    | I.Null, V -> V
    | I.Decl (K', EV (I.EVar (_, GX, VX, _))), V ->
        (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        let V' = raiseType (GX, VX) in
        let V'' = abstractExp (K', 0, (V', I.id)) in
        abstractKPi (K', I.Pi ((I.Dec (None, V''), I.Maybe), V))
    | I.Decl (K', FV (name, V')), V ->
        (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        let V'' = abstractExp (K', 0, (V', I.id)) in
        abstractKPi (K', I.Pi ((I.Dec (Some name, V''), I.Maybe), V))
    | I.Decl (K', LV (I.LVar (r, _, (l, t)))), V ->
        let t' = abstractSOME (K', t) in
        abstractKPi (K', I.Pi ((I.BDec (None, (l, t')), I.Maybe), V))
  (* abstractKLam (K, U) = U'
       where U' = [[K]] U

       Invariant:
       If   {{K}} |- U : V
       and  . ||- U
       and  . ||- V

       then U' = [[K]] U
       and  . |- U' : {{K}} V
       and  . ||- U'
    *)

  let rec abstractKLam = function
    | I.Null, U -> U
    | I.Decl (K', EV (I.EVar (_, GX, VX, _))), U ->
        let V' = raiseType (GX, VX) in
        abstractKLam
          (K', I.Lam (I.Dec (None, abstractExp (K', 0, (V', I.id))), U))
    | I.Decl (K', FV (name, V')), U ->
        abstractKLam
          (K', I.Lam (I.Dec (Some name, abstractExp (K', 0, (V', I.id))), U))

  let rec abstractKCtx = function
    | I.Null -> I.Null
    | I.Decl (K', EV (I.EVar (_, GX, VX, _))) ->
        (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        let V' = raiseType (GX, VX) in
        let V'' = abstractExp (K', 0, (V', I.id)) in
        I.Decl (abstractKCtx K', I.Dec (None, V''))
    | I.Decl (K', FV (name, V')) ->
        (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        let V'' = abstractExp (K', 0, (V', I.id)) in
        I.Decl (abstractKCtx K', I.Dec (Some name, V''))
    | I.Decl (K', LV (I.LVar (r, _, (l, t)))) ->
        let t' = abstractSOME (K', t) in
        I.Decl (abstractKCtx K', I.BDec (None, (l, t')))
  (* abstractDecImp V = (k', V')   (* rename --cs  (see above) *)

       Invariant:
       If    . |- V : L
       and   K ||- V

       then  . |- V' : L
       and   V' = {{K}} V
       and   . ||- V'
       and   k' = |K|
    *)

  let rec abstractDecImp V =
    let K = collectExp (I.Null, (V, I.id), I.Null) in
    let _ = checkConstraints K in
    (I.ctxLength K, abstractKPi (K, abstractExp (K, 0, (V, I.id))))
  (* abstractDef U V = (k', (U', V'))

       Invariant:
       If    . |- V : L
       and   . |- U : V
       and   K1 ||- V
       and   K2 ||- U
       and   K = K1, K2

       then  . |- V' : L
       and   V' = {{K}} V
       and   . |- U' : V'
       and   U' = [[K]] U
       and   . ||- V'
       and   . ||- U'
       and   k' = |K|
    *)

  let rec abstractDef U V =
    let K =
      collectExp (I.Null, (U, I.id), collectExp (I.Null, (V, I.id), I.Null))
    in
    let _ = checkConstraints K in
    ( I.ctxLength K,
      ( abstractKLam (K, abstractExp (K, 0, (U, I.id))),
        abstractKPi (K, abstractExp (K, 0, (V, I.id))) ) )

  let rec abstractSpineExt S s =
    let K = collectSpine (I.Null, (S, s), I.Null) in
    let _ = checkConstraints K in
    let G = abstractKCtx K in
    let S = abstractSpine (K, 0, (S, s)) in
    (G, S)
  (* abstractCtxs [G1,...,Gn] = G0, [G1',...,Gn']
       Invariants:
       If . |- G1,...,Gn ctx
          K ||- G1,...,Gn for_sml some K
       then G0 |- G1',...,Gn' ctx for_sml G0 = {{K}}
       and G1',...,Gn' nf
       and . ||- G1',...,Gn' ctx
    *)

  let rec abstractCtxs Gs =
    let K = collectCtxs (I.Null, Gs, I.Null) in
    let _ = checkConstraints K in
    (abstractKCtx K, abstractCtxlist (K, 0, Gs))
  (* closedDec (G, D) = true iff D contains no EVar or FVar *)

  let rec closedDec (G, (I.Dec (_, V), s)) =
    match collectExp (G, (V, s), I.Null) with I.Null -> true | _ -> false

  let rec closedSub = function
    | G, I.Shift _ -> true
    | G, I.Dot (I.Idx _, s) -> closedSub (G, s)
    | G, I.Dot (I.Exp U, s) -> (
        match collectExp (G, (U, I.id), I.Null) with
        | I.Null -> closedSub (G, s)
        | _ -> false)

  let rec closedExp (G, (U, s)) =
    match collectExp (G, (U, I.id), I.Null) with I.Null -> true | _ -> false

  let rec closedCtx = function
    | I.Null -> true
    | I.Decl (G, D) -> closedCtx G && closedDec (G, (D, I.id))

  let rec closedFor = function
    | Psi, T.True -> true
    | Psi, T.All ((D, _), F) ->
        closedDEC (Psi, D) && closedFor (I.Decl (Psi, D), F)
    | Psi, T.Ex ((D, _), F) ->
        closedDec (T.coerceCtx Psi, (D, I.id))
        && closedFor (I.Decl (Psi, T.UDec D), F)

  and closedDEC = function
    | Psi, T.UDec D -> closedDec (T.coerceCtx Psi, (D, I.id))
    | Psi, T.PDec (_, F, _, _) -> closedFor (Psi, F)

  let rec closedCTX = function
    | I.Null -> true
    | I.Decl (Psi, D) -> closedCTX Psi && closedDEC (Psi, D)

  let rec evarsToK = function
    | [] -> I.Null
    | X :: Xs -> I.Decl (evarsToK Xs, EV X)

  let rec KToEVars = function
    | I.Null -> []
    | I.Decl (K, EV X) -> X :: KToEVars K
    | I.Decl (K, _) -> KToEVars K
  (* collectEVars (G, U[s], Xs) = Xs'
       Invariants:
         G |- U[s] : V
         Xs' extends Xs by new EVars in U[s]
    *)

  let rec collectEVars G Us Xs = KToEVars (collectExp (G, Us, evarsToK Xs))

  let rec collectEVarsSpine (G, (S, s), Xs) =
    KToEVars (collectSpine (G, (S, s), evarsToK Xs))
  (* for_sml the theorem prover:
       collect and abstract in subsitutions  including residual lemmas
       pending approval of Frank.
    *)

  let rec collectPrg = function
    | _, P, K -> I.Decl (K, PV P)
    | Psi, T.Unit, K -> K
    | Psi, T.PairExp (U, P), K ->
        collectPrg (Psi, P, collectExp (T.coerceCtx Psi, (U, I.id), K))
  (* abstractPVar (K, depth, L) = C'

       Invariant:
       If   G |- L : V
       and  |G| = depth
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)

  let rec abstractPVar = function
    | I.Decl (K', PV (T.EVar (_, r', _, _, _, _))), depth, P ->
        if r = r' then T.Var (depth + 1) else abstractPVar (K', depth + 1, P)
    | I.Decl (K', _), depth, P -> abstractPVar (K', depth + 1, P)

  let rec abstractPrg = function
    | K, depth, X -> abstractPVar (K, depth, X)
    | K, depth, T.Unit -> T.Unit
    | K, depth, T.PairExp (U, P) ->
        T.PairExp (abstractExp (K, depth, (U, I.id)), abstractPrg (K, depth, P))

  let rec collectTomegaSub = function
    | T.Shift 0 -> I.Null
    | T.Dot (T.Exp U, t) -> collectExp (I.Null, (U, I.id), collectTomegaSub t)
    | T.Dot (T.Block B, t) -> collectBlock (I.Null, B, collectTomegaSub t)
    | T.Dot (T.Prg P, t) -> collectPrg (I.Null, P, collectTomegaSub t)

  let rec abstractOrder = function
    | K, depth, O.Arg (Us1, Us2) ->
        O.Arg
          ( (abstractExp (K, depth, Us1), I.id),
            (abstractExp (K, depth, Us2), I.id) )
    | K, depth, O.Simul Os ->
        O.Simul (map (fun O -> abstractOrder (K, depth, O)) Os)
    | K, depth, O.Lex Os ->
        O.Lex (map (fun O -> abstractOrder (K, depth, O)) Os)

  let rec abstractTC = function
    | K, depth, T.Abs (D, TC) ->
        T.Abs (abstractDec (K, depth, (D, I.id)), abstractTC (K, depth, TC))
    | K, depth, T.Conj (TC1, TC2) ->
        T.Conj (abstractTC (K, depth, TC1), abstractTC (K, depth, TC2))
    | K, depth, T.Base O -> T.Base (abstractOrder (K, depth, O))

  let rec abstractTCOpt = function
    | K, depth, None -> None
    | K, depth, Some TC -> Some (abstractTC (K, depth, TC))

  let rec abstractMetaDec = function
    | K, depth, T.UDec D -> T.UDec (abstractDec (K, depth, (D, I.id)))
    | K, depth, T.PDec (xx, F, TC1, TC2) ->
        T.PDec (xx, abstractFor (K, depth, F), TC1, TC2)

  and abstractFor = function
    | K, depth, T.True -> T.True
    | K, depth, T.All ((MD, Q), F) ->
        T.All ((abstractMetaDec (K, depth, MD), Q), abstractFor (K, depth, F))
    | K, depth, T.Ex ((D, Q), F) ->
        T.Ex ((abstractDec (K, depth, (D, I.id)), Q), abstractFor (K, depth, F))
    | K, depth, T.And (F1, F2) ->
        T.And (abstractFor (K, depth, F1), abstractFor (K, depth, F2))
    | K, depth, T.World (W, F) -> T.World (W, abstractFor (K, depth, F))

  let rec abstractPsi = function
    | I.Null -> I.Null
    | I.Decl (K', EV (I.EVar (_, GX, VX, _))) ->
        (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        let V' = raiseType (GX, VX) in
        let V'' = abstractExp (K', 0, (V', I.id)) in
        I.Decl (abstractPsi K', T.UDec (I.Dec (None, V'')))
    | I.Decl (K', FV (name, V')) ->
        (* enforced by reconstruction -kw
          val _ = checkType V'' *)
        let V'' = abstractExp (K', 0, (V', I.id)) in
        I.Decl (abstractPsi K', T.UDec (I.Dec (Some name, V'')))
    | I.Decl (K', LV (I.LVar (r, _, (l, t)))) ->
        let t' = abstractSOME (K', t) in
        I.Decl (abstractPsi K', T.UDec (I.BDec (None, (l, t'))))
    | I.Decl (K', PV (T.EVar (GX, _, FX, TC1, TC2, _))) ->
        let F' = abstractFor (K', 0, T.forSub (FX, T.id)) in
        let TC1' = abstractTCOpt (K', 0, TC1) in
        let TC2' = abstractTCOpt (K', 0, TC2) in
        I.Decl (abstractPsi K', T.PDec (None, F', TC1, TC2))

  let rec abstractTomegaSub t =
    let K = collectTomegaSub t in
    let t' = abstractTomegaSub' (K, 0, t) in
    let Psi = abstractPsi K in
    (Psi, t')

  and abstractTomegaSub' = function
    | K, depth, T.Shift 0 -> T.Shift depth
    | K, depth, T.Dot (T.Exp U, t) ->
        T.Dot
          ( T.Exp (abstractExp (K, depth, (U, I.id))),
            abstractTomegaSub' (K, depth, t) )
    | K, depth, T.Dot (T.Block B, t) ->
        T.Dot
          ( T.Block (abstractLVar (K, depth, B)),
            abstractTomegaSub' (K, depth, t) )
    | K, depth, T.Dot (T.Prg P, t) ->
        T.Dot
          (T.Prg (abstractPrg (K, depth, P)), abstractTomegaSub' (K, depth, t))

  let rec abstractTomegaPrg P =
    let K = collectPrg (I.Null, P, I.Null) in
    let P' = abstractPrg (K, 0, P) in
    let Psi = abstractPsi K in
    (Psi, P')
  (* just added to abstract over residual lemmas  -cs *)

  (* Tomorrow: Make collection in program values a priority *)

  (* Then just traverse the Tomega by abstraction to get to the types of those
       variables. *)

  let raiseType = raiseType
  let raiseTerm = raiseTerm
  let piDepend = piDepend
  let closedDec = closedDec
  let closedSub = closedSub
  let closedExp = closedExp
  let abstractDecImp = abstractDecImp
  let abstractDef = abstractDef
  let abstractCtxs = abstractCtxs
  let abstractTomegaSub = abstractTomegaSub
  let abstractTomegaPrg = abstractTomegaPrg
  let abstractSpine = abstractSpineExt
  let collectEVars = collectEVars
  let collectEVarsSpine = collectEVarsSpine
  let closedCtx = closedCtx
  let closedCTX = closedCTX
end

(* functor Abstract *)
