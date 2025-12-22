(* Recursion *)

(* Author: Carsten Schuermann *)

(* See [Rohwedder,Pfenning ESOP'96] *)

module Recursion
    (Global : GLOBAL)
    (MetaSyn' : METASYN)
    (Whnf : WHNF)
    (Unify : UNIFY)
    (Conv : CONV)
    (Names : NAMES)
    (Subordinate : SUBORDINATE)
    (Print : PRINT)
    (Order : ORDER)
    (ModeTable : MODETABLE)
    (Lemma : LEMMA)
    (Filling : FILLING)
    (MetaPrint : METAPRINT)
    (MetaAbstract : METAABSTRACT)
    (Formatter : FORMATTER) : RECURSION = struct
  module MetaSyn = MetaSyn'

  exception Error of string

  type operator = MetaSyn.state

  module M = MetaSyn
  module I = IntSyn
  module O = Order
  module N = Names
  module F = Formatter

  type quantifier = Universal | Existential
  (*     | Ex                      *)

  (* If Q marks all parameters in a context G we write   G : Q               *)

  (* duplicate code? -fp *)

  let rec vectorToString (G, O) =
    let rec fmtOrder = function
      | Order.Arg (Us, Vs) ->
          [
            F.String (Print.expToString (G, I.EClo Us));
            F.String ":";
            F.String (Print.expToString (G, I.EClo Vs));
          ]
      | Order.Lex L -> [ F.String "{"; F.HVbox (fmtOrders L); F.String "}" ]
      | Order.Simul L -> [ F.String "["; F.HVbox (fmtOrders L); F.String "]" ]
    and fmtOrders = function
      | [] -> []
      | O :: [] -> fmtOrder O
      | O :: L -> fmtOrder O @ (F.String " " :: fmtOrders L)
    in
    F.makestring_fmt (F.HVbox (fmtOrder O))
  (* vector (c, (S, s)) = P'

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type
       and  G |- S[s] = U1 .. Un : V[s] > type
       and  sel (c) = i1 .. im
       then P' = (U1'[s1']: V1'[t1'], .., U1'[sm']: V1'[tm'])
       and  G |- sj' : Gj'    Gj' |- Uj' : V1j'
       and  G |- tj' : Gj'    Gj' |- Vj' : L
       and  G |- Vj' [tj'] = V1j' [sj'] : L
       and  G |- Uik = Uk'[sk']
    *)

  let rec vector (c, (S, s)) =
    let Vid = (I.constType c, I.id) in
    let rec select' (n, (Ss', Vs'')) = select'W (n, (Ss', Whnf.whnf Vs''))
    and select'W = function
      | 1, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V''), _), _), s'')) ->
          ((U', s'), (V'', s''))
      | n, ((I.SClo (S', s1'), s2'), Vs'') ->
          select'W (n, ((S', I.comp (s1', s2')), Vs''))
      | n, ((I.App (U', S'), s'), (I.Pi ((I.Dec (_, V1''), _), V2''), s'')) ->
          select'
            (n - 1, ((S', s'), (V2'', I.Dot (I.Exp (I.EClo (U', s')), s''))))
    in
    let rec select = function
      | O.Arg n -> O.Arg (select' (n, ((S, s), Vid)))
      | O.Lex L -> O.Lex (map select L)
      | O.Simul L -> O.Simul (map select L)
    in
    select (O.selLookup c)
  (* set_parameter (G, X, k, sc, ops) = ops'

       Invariant:
       appends a list of recursion operators to ops after
       instantiating X with all possible local parameters (between 1 and k)
    *)

  let rec set_parameter (G, X, k, sc, ops) =
    let rec set_parameter' = function
      | 0, ops' -> ops'
      | k', ops' ->
          let D' = I.ctxDec (G, k') in
          let ops'' =
            CSManager.trail (fun () ->
                if
                  Unify.unifiable (G, (V, I.id), (V', I.id))
                  && Unify.unifiable
                       (G, (X, I.id), (I.Root (I.BVar k', I.Nil), I.id))
                then sc ops'
                else ops')
          in
          set_parameter' (k' - 1, ops'')
    in
    set_parameter' (k, ops)
  (* ltinit (G, k, ((U1, s1), (V2, s2)), ((U3, s3), (V4, s4)), sc, ops) = ops'

       Invariant:
       If   G = G0, Gp    (G0, global context, Gp, parameter context)
       and  |Gp| = k
       and  G |- s1 : G1   G1 |- U1 : V1
       and  G |- s2 : G2   G2 |- V2 : L
            G |- s3 : G1   G1 |- U3 : V3
       and  G |- s4 : G2   G2 |- V4 : L
       and  G |- V1[s1] == V2 [s2]
       and  G |- V3[s3] == V4 [s5]
       and  ops is a set of all all possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators
    *)

  let rec ltinit (G, k, (Us, Vs), UsVs', sc, ops) =
    ltinitW (G, k, Whnf.whnfEta (Us, Vs), UsVs', sc, ops)

  and ltinitW = function
    | G, k, (Us, Vs), UsVs', sc, ops -> lt (G, k, (Us, Vs), UsVs', sc, ops)
    | ( G,
        k,
        ((I.Lam (D1, U), s1), (I.Pi (D2, V), s2)),
        ((U', s1'), (V', s2')),
        sc,
        ops ) ->
        ltinit
          ( I.Decl (G, I.decSub (D1, s1) (* = I.decSub (D2, s2) *)),
            k + 1,
            ((U, I.dot1 s1), (V, I.dot1 s2)),
            ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))),
            sc,
            ops )

  and lt (G, k, (Us, Vs), (Us', Vs'), sc, ops) =
    ltW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ops)

  and ltW = function
    | G, k, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc, ops ->
        ltSpine (G, k, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, ops)
    | G, k, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc, ops ->
        if n <= k then (* n must be a local variable *)
          let (I.Dec (_, V')) = I.ctxDec (G, n) in
          ltSpine (G, k, (Us, Vs), ((S', s'), (V', I.id)), sc, ops)
        else ops
    | G, _, _, ((I.EVar _, _), _), _, ops -> ops
    | ( G,
        k,
        ((U, s1), (V, s2)),
        ((I.Lam (D, U'), s1'), (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
        sc,
        ops ) ->
        if
          Subordinate.equiv (I.targetFam V, I.targetFam V1')
          (* == I.targetFam V2' *)
        then
          (* enforce that X gets only bound to parameters *)
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' = fun ops' -> set_parameter (G, X, k, sc, ops') in
          lt
            ( G,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc',
              ops )
        else if Subordinate.below (I.targetFam V1', I.targetFam V) then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          lt
            ( G,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc,
              ops )
        else ops

  and ltSpine (G, k, (Us, Vs), (Ss', Vs'), sc, ops) =
    ltSpineW (G, k, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, ops)

  and ltSpineW = function
    | G, k, (Us, Vs), ((I.Nil, _), _), _, ops -> ops
    | G, k, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, ops ->
        ltSpineW (G, k, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, ops)
    | ( G,
        k,
        (Us, Vs),
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        sc,
        ops ) ->
        let ops' = le (G, k, (Us, Vs), ((U', s1'), (V1', s2')), sc, ops) in
        ltSpine
          ( G,
            k,
            (Us, Vs),
            ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
            sc,
            ops' )

  and eq (G, (Us, Vs), (Us', Vs'), sc, ops) =
    CSManager.trail (fun () ->
        if Unify.unifiable (G, Vs, Vs') && Unify.unifiable (G, Us, Us') then
          sc ops
        else ops)

  and le (G, k, (Us, Vs), (Us', Vs'), sc, ops) =
    let ops' = eq (G, (Us, Vs), (Us', Vs'), sc, ops) in
    leW (G, k, (Us, Vs), Whnf.whnfEta (Us', Vs'), sc, ops')

  and leW = function
    | ( G,
        k,
        ((U, s1), (V, s2)),
        ((I.Lam (D, U'), s1'), (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
        sc,
        ops ) ->
        if
          Subordinate.equiv (I.targetFam V, I.targetFam V1')
          (* == I.targetFam V2' *)
        then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          (* enforces that X can only bound to parameter *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' = fun ops' -> set_parameter (G, X, k, sc, ops') in
          le
            ( G,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc',
              ops )
        else if Subordinate.below (I.targetFam V1', I.targetFam V) then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          le
            ( G,
              k,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc,
              ops )
        else ops
    | G, k, (Us, Vs), (Us', Vs'), sc, ops ->
        lt (G, k, (Us, Vs), (Us', Vs'), sc, ops)
  (* ordlt (G, O1, O2, sc, ops) = ops'

       Invariant:
       If   G |- O1 augmented subterms
       and  G |- O2 augmented subterms
       and  ops is a set of already calculuated possible states
       and  sc is success continuation
       then ops' is an extension of ops, containing all
            recursion operators of all instantiations of EVars s.t. O1 is
            lexicographically smaller than O2
    *)

  let rec ordlt = function
    | G, O.Arg UsVs, O.Arg UsVs', sc, ops -> ltinit (G, 0, UsVs, UsVs', sc, ops)
    | G, O.Lex L, O.Lex L', sc, ops -> ordltLex (G, L, L', sc, ops)
    | G, O.Simul L, O.Simul L', sc, ops -> ordltSimul (G, L, L', sc, ops)

  and ordltLex = function
    | G, [], [], sc, ops -> ops
    | G, O :: L, O' :: L', sc, ops ->
        let ops' = CSManager.trail (fun () -> ordlt (G, O, O', sc, ops)) in
        ordeq (G, O, O', fun ops'' -> (ordltLex (G, L, L', sc, ops''), ops'))

  and ordltSimul = function
    | G, [], [], sc, ops -> ops
    | G, O :: L, O' :: L', sc, ops ->
        let ops'' =
          CSManager.trail (fun () ->
              ordlt
                (G, O, O', fun ops' -> (ordleSimul (G, L, L', sc, ops'), ops)))
        in
        ordeq (G, O, O', fun ops' -> (ordltSimul (G, L, L', sc, ops'), ops''))

  and ordleSimul = function
    | G, [], [], sc, ops -> sc ops
    | G, O :: L, O' :: L', sc, ops ->
        ordle (G, O, O', fun ops' -> (ordleSimul (G, L, L', sc, ops'), ops))

  and ordeq = function
    | G, O.Arg (Us, Vs), O.Arg (Us', Vs'), sc, ops ->
        if Unify.unifiable (G, Vs, Vs') && Unify.unifiable (G, Us, Us') then
          sc ops
        else ops
    | G, O.Lex L, O.Lex L', sc, ops -> ordeqs (G, L, L', sc, ops)
    | G, O.Simul L, O.Simul L', sc, ops -> ordeqs (G, L, L', sc, ops)

  and ordeqs = function
    | G, [], [], sc, ops -> sc ops
    | G, O :: L, O' :: L', sc, ops ->
        ordeq (G, O, O', fun ops' -> (ordeqs (G, L, L', sc, ops'), ops))

  and ordle (G, O, O', sc, ops) =
    let ops' = CSManager.trail (fun () -> ordeq (G, O, O', sc, ops)) in
    ordlt (G, O, O', sc, ops')
  (* createEVars (G, M) = ((G', M'), s')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
    *)

  let rec createEVars = function
    | M.Prefix (I.Null, I.Null, I.Null) ->
        (M.Prefix (I.Null, I.Null, I.Null), I.id)
    | M.Prefix (I.Decl (G, D), I.Decl (M, M.Top), I.Decl (B, b)) ->
        let M.Prefix (G', M', B'), s' = createEVars (M.Prefix (G, M, B)) in
        ( M.Prefix
            (I.Decl (G', I.decSub (D, s')), I.Decl (M', M.Top), I.Decl (B', b)),
          I.dot1 s' )
    | M.Prefix (I.Decl (G, I.Dec (_, V)), I.Decl (M, M.Bot), I.Decl (B, _)) ->
        let M.Prefix (G', M', B'), s' = createEVars (M.Prefix (G, M, B)) in
        let X = I.newEVar (G', I.EClo (V, s')) in
        (M.Prefix (G', M', B'), I.Dot (I.Exp X, s'))
  (* select (G, (V, s)) = (G', (V1', s1'), (V2', s2'))

     Invariant:
     If   G |- s : G1   G1 |- V : type
     and  G |- V [s] = {V1} ... {Vn} a S
     then G' = G, V1 .. Vn
     and  G' |- s1' : G1'   G1' |- V1' : type
     and  G' |- s2' : G2'   G2' |- V2' : type
     and  G' |- V1' [s1'] = V1 [^n]
     and  G' |- V2' [s2'] = a S
    *)

  let rec select (G, Vs) = selectW (G, Whnf.whnf Vs)

  and selectW (G, (I.Pi ((D, _), V2), s)) =
    let rec select' (G, (Vs1, Vs2)) = selectW' (G, (Vs1, Whnf.whnf Vs2))
    and selectW' = function
      | G, (Vs1, Vs2) -> (G, (Vs1, Vs2))
      | G, ((V1, s1), (I.Pi ((D, P), V2'), s2)) ->
          select'
            ( I.Decl (G, I.decSub (D, s2)),
              ((V1, I.comp (s1, I.shift)), (V2', I.dot1 s2)) )
    in
    select'
      (I.Decl (G, I.decSub (D, s)), ((V1, I.comp (s, I.shift)), (V2, I.dot1 s)))
  (* lemma (S, t, ops) = (G', P', P'', abstract', ops')

       Invariant:
       If   S state  (S = ((G, M), V)
                     |- G ctx
                     G |- M mtx
                     G |- V = {V1} ... {Vn} a S)
       and  S' state derived from S by an inductive call to t
       and  ops a list of operators
       then G is context, where all - variables are replaced by EVars in S'
       and  P' is induction variable vector of EVars in the inductive call
       and  P'' is induction variable vector of the theorem S.
       and  G' |- P' : (V1' .. Vn')
              (where  t : {W1} ..{Wm} b S, and Vi' are among W1 .. Wm)
       and  G'' |- P'' : (V1'' .. Vn'')
              (where  a : {W1} ..{Wm} b S, and Vi'' are among W1 .. Wm)

    *)

  let rec lemma (S, t, ops) =
    let (M.State (name, GM, V)) = Lemma.apply (S, t) in
    let M.Prefix (G', M', B'), s' = createEVars GM in
    let G'', ((I.Root (I.Const a1, S1), s1), (I.Root (I.Const a2, S2), s2)) =
      select (G', (V, s'))
    in
    ( G'',
      vector (a1, (S1, s1)),
      vector (a2, (S2, s2)),
      fun ops' ->
        ( MetaAbstract.abstract
            (M.State (name, M.Prefix (G', M', B'), I.EClo (V, s')))
          :: ops',
          ops ) )
  (* expandLazy' (S, L, ops) = ops'

       Invariant:
       If   S state
       and  L list of mutual recursive type families
       and  ops a list of operators
       then ops' extends ops by all operators
         representing inductive calls to theorems in L
    *)

  let rec expandLazy' = function
    | S, O.Empty, ops -> ops
    | S, O.LE (t, L), ops -> expandLazy' (S, L, ordle (lemma (S, t, ops)))
    | S, O.LT (t, L), ops -> expandLazy' (S, L, ordlt (lemma (S, t, ops)))

  let rec recursionDepth V =
    let rec recursionDepth' = function
      | I.Root _, n -> n
      | I.Pi (_, V), n -> recursionDepth' (V, n + 1)
    in
    recursionDepth' (V, 0)
  (* expandLazy S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (only induction variables are instantiated)
    *)

  let rec expandLazy S =
    if recursionDepth V > !MetaGlobal.maxRecurse then []
    else expandLazy' (S, O.mutLookup (I.targetFam V), [])
  (* inputConv ((V1, s1), (V2, s2)) = B

       Invariant:
       If  G |- s1 : G1   G1 |- V1 : L
       and G |- s2 : G2   G2 |- V2 : L
       and G |- V1[s1] = c1 ; S1
       and G |- V2[s2] = c2 ; S2
       then B' holds iff c1 =  c2 and V1[s1] ==+ V2[s2]   (convertible on + arguments of c1)
    *)

  let rec inputConv (Vs1, Vs2) = inputConvW (Whnf.whnf Vs1, Whnf.whnf Vs2)

  and inputConvW ((I.Root (I.Const c1, S1), s1), (I.Root (I.Const c2, S2), s2))
      =
    (* s1 = s2 = id *)
    if c1 = c2 then
      inputConvSpine
        ( valOf (ModeTable.modeLookup c1),
          ((S1, s1), (I.constType c1, I.id)),
          ((S2, s2), (I.constType c2, I.id)) )
    else false

  and inputConvSpine = function
    | ModeSyn.Mnil, ((S1, _), _), ((S2, _), _) -> true
    | mS, ((I.SClo (S1, s1'), s1), Vs1), (Ss2, Vs2) ->
        inputConvSpine (mS, ((S1, I.comp (s1', s1)), Vs1), (Ss2, Vs2))
    | mS, (Ss1, Vs1), ((I.SClo (S2, s2'), s2), Vs2) ->
        inputConvSpine (mS, (Ss1, Vs1), ((S2, I.comp (s2', s2)), Vs2))
    | ( ModeSyn.Mapp (ModeSyn.Marg (ModeSyn.Minus, _), mS),
        ((I.App (U1, S1), s1), (I.Pi ((I.Dec (_, V1), _), W1), t1)),
        ((I.App (U2, S2), s2), (I.Pi ((I.Dec (_, V2), _), W2), t2)) ) ->
        Conv.conv ((V1, t1), (V2, t2))
        && inputConvSpine
             ( mS,
               ((S1, s1), (W1, I.Dot (I.Exp (I.EClo (U1, s1)), t1))),
               ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U1, s1)), t2))) )
    | ( ModeSyn.Mapp (ModeSyn.Marg (ModeSyn.Plus, _), mS),
        ((I.App (U1, S1), s1), (I.Pi ((I.Dec (_, V1), _), W1), t1)),
        ((I.App (U2, S2), s2), (I.Pi ((I.Dec (_, V2), _), W2), t2)) ) ->
        inputConvSpine
          ( mS,
            ((S1, s1), (W1, I.Dot (I.Exp (I.EClo (U1, s1)), t1))),
            ((S2, s2), (W2, I.Dot (I.Exp (I.EClo (U2, s2)), t2))) )
  (* removeDuplicates ops = ops'

       Invariant:
       If   ops is a list of recursion operators,
       then ops' is a sublist of ops, s.t.
         forall S = ((G, M), V) in ops'
               |- G ctx
               G |- M mtx
               G |- V = {V0} .. {Vn} a ; S : type
               and Vi = ci ; S'
               and forall 1 <= i <= n:
                 either ci =/= c0 orelse
                 G, V0 .. Vi |- V0 [^ i] =/=+ Vi (not convertible on + arguments on c0)
    *)

  let rec removeDuplicates = function
    | [] -> []
    | S' :: ops ->
        let rec compExp (Vs1, Vs2) = compExpW (Whnf.whnf Vs1, Whnf.whnf Vs2)
        and compExpW = function
          | Vs1, (I.Root _, _) -> false
          | Vs1, (I.Pi ((D2, _), V2), s2) ->
              compDec (Vs1, (D2, s2))
              || compExp ((V1, I.comp (s1, I.shift)), (V2, I.dot1 s2))
        and compDec (Vs1, (I.Dec (_, V2), s2)) = inputConv (Vs1, (V2, s2)) in
        let rec check (M.State (name, GM, V)) = checkW (Whnf.whnf (V, I.id))
        and checkW (I.Pi ((D, _), V), s) =
          checkDec ((D, I.comp (s, I.shift)), (V, I.dot1 s))
        and checkDec ((I.Dec (_, V1), s1), Vs2) = compExp ((V1, s1), Vs2) in
        if check S' then removeDuplicates ops else S' :: removeDuplicates ops
  (* fillOps ops = ops'

       Invariant:
       If   ops is a list of lazy recursion operators
       then ops' is a list of recursion operators combined with a filling
         operator to fill non-index variables.
    *)

  let rec fillOps = function
    | [] -> []
    | S' :: ops ->
        let rec fillOps' = function [] -> [] | O :: _ -> Filling.apply O in
        let fillop, _ = Filling.expand S' in
        fillOps' fillop @ fillOps ops
  (* expandEager S = ops'

       Invariant:
       If   S State
       then ops' a list of operations which cause a recursive call
         (all variables of recursive call are instantiated)
    *)

  let rec expandEager S = removeDuplicates (fillOps (expandLazy S))
  let rec apply S = S
  let rec menu S = "Recursion : " ^ Print.expToString (G', V)
  let rec handleExceptions f P = try f P with Order.Error s -> raise (Error s)
  let expandLazy = handleExceptions expandLazy
  let expandEager = handleExceptions expandEager
  let apply = apply
  let menu = menu
  (* local *)
end

(* functor Recursion *)
(* Recursion *)

(* Author: Carsten Schuermann *)

module type RECURSION = sig
  module MetaSyn : METASYN

  exception Error of string

  type operator

  val expandLazy : MetaSyn.state -> operator list
  val expandEager : MetaSyn.state -> operator list
  val apply : operator -> MetaSyn.state
  val menu : operator -> string
end

(* signature RECURSION *)
