open Basis

(* Reasoning about orders *)

(* Author: Brigitte Pientka *)

module type CHECKING = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  module Order : Order.Order.ORDER

  (*! structure Paths : Paths.PATHS !*)
  (* If Q marks all parameters in a context G we write   G : Q  *)
  type quantifier = All | Exist | And of Paths.occ

  (*     | And                     *)
  type 'a predicate =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec * 'a predicate

  type order = IntSyn.eclo * IntSyn.eclo Order.order

  (* reduction predicate context (unordered) *)
  type rctx = order predicate list

  (* mixed-prefix context *)
  type qctx = quantifier IntSyn.ctx

  val shiftRCtx : rctx -> (IntSyn.sub -> IntSyn.sub) -> rctx

  val shiftPred :
    order predicate -> (IntSyn.sub -> IntSyn.sub) -> order predicate

  val deduce : IntSyn.dctx * qctx * rctx * order predicate -> bool
end

(* signature CHECKING *)
(* Reasoning about structural orders *)

(* Author: Brigitte Pientka *)

(* for_sml reasoning about orders see [Pientka IJCAR'01] *)

module Checking
    (Global : Global.GLOBAL)
    (Whnf : Whnf.WHNF)
    (Conv : Conv.CONV)
    (Unify : Unify.UNIFY)
    (Names : Names.NAMES)
    (Index : Index.INDEX)
    (Subordinate : Subordinate.SUBORDINATE)
    (Formatter : Formatter.FORMATTER)
    (Print : Print.PRINT)
    (Order : Order.Order.ORDER)
    (Origins : Origins.ORIGINS) : CHECKING = struct
  (*! structure IntSyn = IntSyn' !*)

  module Order = Order
  (*! structure Paths = Paths !*)

  type quantifier = All | Exist | And of Paths.occ
  (*     | And                     *)

  (* If Q marks all parameters in a context G we write   G : Q               *)

  type 'a predicate =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec * 'a predicate
  (* Abbreviation *)

  type order = IntSyn.eclo * IntSyn.eclo Order.order
  (* reduction order assumptions (unordered) *)

  type rctx = order predicate list
  (* mixed prefix order contex *)

  type qctx = quantifier IntSyn.ctx

  module I = IntSyn
  module P = Paths
  module N = Names
  module F = Formatter
  module R = Order
  (* Reasoning about order relations *)

  (*
    Typing context        G
    mixed prefix context  Q  := . | All | Existental

    Orders                0  := U[s1] : V[s2] | Lex O1 ... On | Simul O1 ... On
    Order Relation        P  := O < O' | O <= O' | O = O'

    Atomic Order Relation P' := U[s1] : V[s2] <  U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] <= U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] =  U'[s1'] : V'[s2']

    Order Relation Ctx    D  := . | R , D
    Atomic Order Rel. Ctx D' := . | R',  D'

    Invariant:

    sometimes we write G |- an abbreviation

    if P = (O < O')    then G |- O and G |- O'
    if P = (O <= O')    then G |- O and G |- O'
    if P = (O = O')    then G |- O and G |- O'

    if O = Lex O1 .. On  then G |- O1 and ....G |- On
    if O = Simul O1 .. On  then G |- O1 and ....G |- On

    if O = U[s1] : V[s2]
      then     G : Q
           and G |- s1 : G1, G1 |- U : V1
           and G |- s2 : G2   G2 |- V : L
           and G |- U[s1] : V[s2]

  *)

  (*--------------------------------------------------------------------*)

  (* Printing atomic orders *)

  let rec atomicPredToString = function
    | G, Less ((Us, _), (Us', _)) ->
        Print.expToString (G, I.EClo Us)
        ^ " < "
        ^ Print.expToString (G, I.EClo Us')
    | G, Leq ((Us, _), (Us', _)) ->
        Print.expToString (G, I.EClo Us)
        ^ " <= "
        ^ Print.expToString (G, I.EClo Us')
    | G, Eq ((Us, _), (Us', _)) ->
        Print.expToString (G, I.EClo Us)
        ^ " = "
        ^ Print.expToString (G, I.EClo Us')

  let rec atomicRCtxToString = function
    | G, [] -> " "
    | G, O :: [] -> atomicPredToString (G, O)
    | G, O :: D' -> atomicRCtxToString (G, D') ^ ", " ^ atomicPredToString (G, O)
  (*--------------------------------------------------------------------*)

  (* shifting substitutions *)

  (* shiftO O f = O'

      if O is an order
         then we shift the substitutions which are associated
         with its terms by applying f to it
    *)

  let rec shiftO = function
    | R.Arg ((U, us), (V, vs)), f -> R.Arg ((U, f us), (V, f vs))
    | R.Lex L, f -> R.Lex (map (fun O -> shiftO O f) L)
    | R.Simul L, f -> R.Simul (map (fun O -> shiftO O f) L)

  let rec shiftP = function
    | Less (O1, O2), f -> Less (shiftO O1 f, shiftO O2 f)
    | Leq (O1, O2), f -> Leq (shiftO O1 f, shiftO O2 f)
    | Eq (O1, O2), f -> Eq (shiftO O1 f, shiftO O2 f)
    | Pi (D, P), f -> Pi (D, shiftP P f)

  let rec shiftRCtx Rl f = map (fun p -> shiftP p f) Rl

  let rec shiftArg = function
    | Less (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2'))), f ->
        Less (((U1, f s1), (V1, f s1')), ((U2, f s2), (V2, f s2')))
    | Leq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2'))), f ->
        Leq (((U1, f s1), (V1, f s1')), ((U2, f s2), (V2, f s2')))
    | Eq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2'))), f ->
        Eq (((U1, f s1), (V1, f s1')), ((U2, f s2), (V2, f s2')))

  let rec shiftACtx Rl f = map (fun p -> shiftArg p f) Rl
  (*--------------------------------------------------------------------*)

  (* Printing *)

  let rec fmtOrder (G, O) =
    let rec fmtOrder' = function
      | R.Arg (Us, Vs) ->
          F.Hbox [ F.String "("; Print.formatExp (G, I.EClo Us); F.String ")" ]
      | R.Lex L ->
          F.Hbox
            [ F.String "{"; F.HOVbox0 (1, 0, 1, fmtOrders L); F.String "}" ]
      | R.Simul L ->
          F.Hbox
            [ F.String "["; F.HOVbox0 (1, 0, 1, fmtOrders L); F.String "]" ]
    and fmtOrders = function
      | [] -> []
      | [ O ] -> [ fmtOrder' O ]
      | O :: L -> fmtOrder' O :: F.Break :: fmtOrders L
    in
    fmtOrder' O

  let rec fmtComparison (G, O, comp, O') =
    F.HOVbox0
      ( 1,
        0,
        1,
        [ fmtOrder (G, O); F.Break; F.String comp; F.Break; fmtOrder (G, O') ]
      )

  let rec fmtPredicate' = function
    | G, Less (O, O') -> fmtComparison (G, O, "<", O')
    | G, Leq (O, O') -> fmtComparison (G, O, "<=", O')
    | G, Eq (O, O') -> fmtComparison (G, O, "=", O')
    | G, Pi (D, P) ->
        F.Hbox [ F.String "Pi "; fmtPredicate' (I.Decl (G, D), P) ]

  let rec fmtPredicate (G, P) = fmtPredicate' (Names.ctxName G, P)

  let rec fmtRGCtx' = function
    | G, [] -> ""
    | G, [ P ] -> F.makestring_fmt (fmtPredicate' (G, P))
    | G, P :: Rl ->
        F.makestring_fmt (fmtPredicate' (G, P)) ^ " ," ^ fmtRGCtx' (G, Rl)

  let rec fmtRGCtx (G, Rl) = fmtRGCtx' (Names.ctxName G, Rl)
  (*--------------------------------------------------------------------*)

  (* init () = true

       Invariant:
       The inital constraint continuation
    *)

  let rec init () = true
  let rec eqCid (c, c') = c = c'

  let rec conv ((Us, Vs), (Us', Vs')) =
    Conv.conv (Vs, Vs') && Conv.conv (Us, Us')

  let rec isUniversal = function
    | All -> true
    | Exist -> false
    | Exist' -> false

  let rec isExistential = function
    | All -> false
    | Exist -> true
    | Exist' -> true
  (* isParameter (Q, X) = B

       Invariant:
       If   G |- X : V
       and  G : Q
       then B holds iff X is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)

  let rec isParameter (Q, X) = isParameterW (Q, Whnf.whnf (X, I.id))

  and isParameterW (Q, Us) =
    try isUniversal (I.ctxLookup (Q, Whnf.etaContract (I.EClo Us)))
    with Whnf.Eta -> isFreeEVar Us

  and isFreeEVar = function
    | I.EVar (_, _, _, { contents = [] }), _ -> true
    | I.Lam (D, U), s -> isFreeEVar (Whnf.whnf (U, I.dot1 s))
    | _ -> false
  (* isAtomic (G, X) = true
       Invariant:
       If G |- X : V
       and G : Q
       then B holds iff X is an atomic term which is not a parameter
     *)

  let rec isAtomic (GQ, Us) = isAtomicW (GQ, Whnf.whnf Us)

  and isAtomicW = function
    | GQ, (X, s) -> isAtomicS (GQ, (S, s))
    | GQ, (X, s) -> isAtomicS (GQ, (S, s))
    | GQ, (X, s) -> isExistential (I.ctxLookup (Q, n)) || isAtomicS (GQ, (S, s))
    | GQ, _ -> false

  and isAtomicS = function
    | GQ, (I.Nil, _) -> true
    | GQ, (I.SClo (S, s'), s'') -> isAtomicS (GQ, (S, I.comp (s', s'')))
    | GQ, (I.App (U', S'), s1') -> false
  (*-----------------------------------------------------------*)

  (* eq (G, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B

       Invariant:
       B holds  iff
            G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
    *)

  let rec eq (G, (Us, Vs), (Us', Vs')) =
    Unify.unifiable (G, Vs, Vs') && Unify.unifiable (G, Us, Us')
  (* lookupEq (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
     or
     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1' unifies with UsVs and
             UsVs1 unifies with UsVs' and
             all restrictions in sc are satisfied
             (symmetry)


    *)

  let rec lookupEq = function
    | GQ, [], UsVs, UsVs', sc -> false
    | GQ, Less (_, _) :: D, UsVs, UsVs', sc -> lookupEq (GQ, D, UsVs, UsVs', sc)
    | GQ, Eq (UsVs1, UsVs1') :: D, UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () ->
            eq (G, UsVs1, UsVs) && eq (G, UsVs1', UsVs') && sc ())
        || Cs.CSManager.trail (fun () ->
            eq (G, UsVs1, UsVs') && eq (G, UsVs1', UsVs) && sc ())
        || lookupEq (GQ, D, UsVs, UsVs', sc)
  (* lookupLt (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Less(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
    *)

  let rec lookupLt = function
    | GQ, [], UsVs, UsVs', sc -> false
    | GQ, Eq (_, _) :: D, UsVs, UsVs', sc -> lookupLt (GQ, D, UsVs, UsVs', sc)
    | GQ, Less (UsVs1, UsVs1') :: D, UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () ->
            eq (G, UsVs1, UsVs) && eq (G, UsVs1', UsVs') && sc ())
        || lookupLt (GQ, D, UsVs, UsVs', sc)
  (*  eqAtomic (GQ, D, D', UsVs, UsVs', sc) = B

        B iff
            UsVs unifies with UsVs'                (identity)
        or  D, UsVs = UsVs', D' ---> UsVs = UsVs'  (ctx lookup)
        or  D, UsVs' = UsVs, D' ---> UsVs = UsVs'  (ctx lookup + symmetry)
        or  D, D' ---> UsVs = UsVs' by transitivity

     *)

  let rec eqAtomic = function
    | GQ, [], D', UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () -> eq (G, UsVs, UsVs') && sc ())
        || lookupEq (GQ, D', UsVs, UsVs', sc)
    | GQ, D, D', UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () -> eq (G, UsVs, UsVs') && sc ())
        || lookupEq (GQ, D, UsVs, UsVs', sc)
        || lookupEq (GQ, D', UsVs, UsVs', sc)
        || transEq (GQ, D, D', UsVs, UsVs', sc)

  and transEq = function
    | GQ, [], D, UsVs, UsVs', sc -> false
    | GQ, Eq (UsVs1, UsVs1') :: D, D', UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () ->
            eq (G, UsVs1', UsVs')
            && sc ()
            && eqAtomicR (GQ, D @ D', UsVs, UsVs1, sc, atomic))
        || Cs.CSManager.trail (fun () ->
            eq (G, UsVs1, UsVs')
            && sc ()
            && eqAtomicR (GQ, D @ D', UsVs, UsVs1', sc, atomic))
        || transEq (GQ, D, Eq (UsVs1, UsVs1') :: D', UsVs, UsVs', sc)
    | GQ, Less (UsVs1, UsVs1') :: D, D', UsVs, UsVs', sc ->
        transEq (GQ, D, D', UsVs, UsVs', sc)

  and ltAtomic = function
    | GQ, [], D', UsVs, UsVs', sc -> lookupLt (GQ, D', UsVs, UsVs', sc)
    | GQ, D, D', UsVs, UsVs', sc ->
        lookupLt (GQ, D, UsVs, UsVs', sc)
        || lookupLt (GQ, D', UsVs, UsVs', sc)
        || transLt (GQ, D, D', UsVs, UsVs', sc)

  and transLt = function
    | GQ, [], D, UsVs, UsVs', sc -> false
    | GQ, Eq (UsVs1, UsVs1') :: D, D', UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () ->
            eq (G, UsVs1', UsVs')
            && sc ()
            && ltAtomicR (GQ, D @ D', UsVs, UsVs1, sc, atomic))
        || Cs.CSManager.trail (fun () ->
            eq (G, UsVs1, UsVs')
            && sc ()
            && ltAtomicR (GQ, D @ D', UsVs, UsVs1', sc, atomic))
        || transLt (GQ, D, Eq (UsVs1, UsVs1') :: D', UsVs, UsVs', sc)
    | GQ, Less (UsVs1, UsVs1') :: D, D', UsVs, UsVs', sc ->
        Cs.CSManager.trail (fun () ->
            eq (G, UsVs1', UsVs')
            && sc ()
            && eqAtomicR (GQ, D @ D', UsVs, UsVs1, sc, atomic))
        || Cs.CSManager.trail (fun () ->
            eq (G, UsVs1', UsVs')
            && sc ()
            && ltAtomicR (GQ, D @ D', UsVs, UsVs1, sc, atomic))
        || transLt (GQ, D, Less (UsVs1, UsVs1') :: D', UsVs, UsVs', sc)

  and atomic = function
    | GQ, D, D', Eq (UsVs, UsVs'), sc -> eqAtomic (GQ, D, D', UsVs, UsVs', sc)
    | GQ, D, D', Less (UsVs, UsVs'), sc -> ltAtomic (GQ, D, D', UsVs, UsVs', sc)

  and leftInstantiate = function
    | GQ, [], D', P, sc ->
        if atomic (GQ, D', [], P, sc) then (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P)
              ^ "\n")
          else ();
          true)
        else (* should never happen by invariant *)
          false
    | GQ, Less (UsVs, UsVs') :: D, D', P, sc ->
        ltInstL (GQ, D, D', UsVs, UsVs', P, sc)
    | GQ, Leq (UsVs, UsVs') :: D, D', P, sc ->
        leInstL (GQ, D, D', UsVs, UsVs', P, sc)
    | GQ, Eq (UsVs, UsVs') :: D, D', P, sc ->
        eqInstL (GQ, D, D', UsVs, UsVs', P, sc)

  and ltInstL (GQ, D, D', UsVs, UsVs', P', sc) =
    ltInstLW (GQ, D, D', Whnf.whnfEta UsVs, UsVs', P', sc)

  and ltInstLW = function
    | ( GQ,
        D,
        D',
        ((I.Lam (Dec, U), s1), (I.Pi ((I.Dec (_, V2), _), V), s2)),
        ((U', s1'), (V', s2')),
        P',
        sc ) ->
        if
          Subordinate.equiv (I.targetFam V', I.targetFam V1)
          (* == I.targetFam V2' *)
        then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          (* enforces that X can only bound to parameter or remain uninstantiated *)
          let X = I.newEVar (G, I.EClo (V1, s1)) in
          let sc' = fun () -> isParameter (Q, X) && sc () in
          ltInstL
            ( (G, Q),
              D,
              D',
              ((U, I.Dot (I.Exp X, s1)), (V, I.Dot (I.Exp X, s2))),
              ((U', s1'), (V', s2')),
              P',
              sc' )
        else if Subordinate.below (I.targetFam V1, I.targetFam V') then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1, s1)) in
          ltInstL
            ( (G, Q),
              D,
              D',
              ((U, I.Dot (I.Exp X, s1)), (V, I.Dot (I.Exp X, s2))),
              ((U', s1'), (V', s2')),
              P',
              sc )
        else false
    | GQ, D, D', UsVs, UsVs', P', sc ->
        leftInstantiate (GQ, D, Less (UsVs, UsVs') :: D', P', sc)

  and leInstL (GQ, D, D', UsVs, UsVs', P', sc) =
    leInstLW (GQ, D, D', Whnf.whnfEta UsVs, UsVs', P', sc)

  and leInstLW = function
    | ( GQ,
        D,
        D',
        ((I.Lam (I.Dec (_, V1), U), s1), (I.Pi ((I.Dec (_, V2), _), V), s2)),
        ((U', s1'), (V', s2')),
        P',
        sc ) ->
        if
          Subordinate.equiv (I.targetFam V', I.targetFam V1)
          (* == I.targetFam V2' *)
        then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          (* enforces that X can only bound to parameter or remain uninstantiated *)
          let X = I.newEVar (G, I.EClo (V1, s1)) in
          let sc' = fun () -> isParameter (Q, X) && sc () in
          leInstL
            ( (G, Q),
              D,
              D',
              ((U, I.Dot (I.Exp X, s1)), (V, I.Dot (I.Exp X, s2))),
              ((U', s1'), (V', s2')),
              P',
              sc' )
        else if Subordinate.below (I.targetFam V1, I.targetFam V') then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1, s1)) in
          leInstL
            ( (G, Q),
              D,
              D',
              ((U, I.Dot (I.Exp X, s1)), (V, I.Dot (I.Exp X, s2))),
              ((U', s1'), (V', s2')),
              P',
              sc )
        else false
    | GQ, D, D', UsVs, UsVs', P, sc ->
        leftInstantiate (GQ, D, Less (UsVs, UsVs') :: D', P, sc)

  and eqInstL (GQ, D, D', UsVs, UsVs', P', sc) =
    eqInstLW (GQ, D, D', Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P', sc)

  and eqInstLW = function
    | ( GQ,
        D,
        D',
        ( (I.Lam (I.Dec (_, V1'), U'), s1'),
          (I.Pi ((I.Dec (_, V2'), _), V'), s2') ),
        ( (I.Lam (I.Dec (_, V1''), U''), s1''),
          (I.Pi ((I.Dec (_, V2''), _), V''), s2'') ),
        P',
        sc ) ->
        (* = I.newEVar (I.EClo (V2', s2')) *)
        let X = I.newEVar (G, I.EClo (V1'', s1'')) in
        eqInstL
          ( GQ,
            D,
            D',
            ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
            ((U'', I.Dot (I.Exp X, s1'')), (V'', I.Dot (I.Exp X, s2''))),
            P',
            fun () ->
              isParameter (Q, X);
              sc () )
    | GQ, D, D', UsVs, UsVs', P', sc -> eqIL (GQ, D, D', UsVs, UsVs', P', sc)

  and eqIL = function
    | GQ, D, D', UsVs, UsVs', P', sc ->
        if eqCid (c, c') then
          eqSpineIL
            ( GQ,
              D,
              D',
              ((S, s), (I.constType c, I.id)),
              ((S', s'), (I.constType c', I.id)),
              P',
              sc )
        else (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, Eq (UsVs, UsVs') :: D)
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P')
              ^ "\n")
          else ();
          true)
    | GQ, D, D', UsVs, UsVs', P', sc ->
        if eqCid (c, c') then
          eqSpineIL
            ( GQ,
              D,
              D',
              ((S, s), (I.constType c, I.id)),
              ((S', s'), (I.constType c', I.id)),
              P',
              sc )
        else (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, Eq (UsVs, UsVs') :: D)
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P')
              ^ "\n")
          else ();
          true)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P', sc ->
        if isAtomic (GQ, Us') then
          leftInstantiate (GQ, D, Eq ((Us', Vs'), (Us, Vs)) :: D', P', sc)
        else (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, Eq ((Us, Vs), (Us', Vs')) :: D)
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P')
              ^ "\n")
          else ();
          true)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P', sc ->
        if isAtomic (GQ, Us') then
          leftInstantiate (GQ, D, Eq ((Us', Vs'), (Us, Vs)) :: D', P', sc)
        else (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, Eq ((Us, Vs), (Us', Vs')) :: D)
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P')
              ^ "\n")
          else ();
          true)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P', sc ->
        if isAtomic (GQ, Us) then
          leftInstantiate (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P', sc)
        else (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, Eq ((Us, Vs), (Us', Vs')) :: D')
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P')
              ^ "\n")
          else ();
          true)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P', sc ->
        if isAtomic (GQ, Us) then
          leftInstantiate (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P', sc)
        else (
          if !Global.chatter > 4 then
            print
              (" Proved: "
              ^ atomicRCtxToString (G, Eq ((Us, Vs), (Us', Vs')) :: D')
              ^ atomicRCtxToString (G, D')
              ^ " ---> "
              ^ atomicPredToString (G, P')
              ^ "\n")
          else ();
          true)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P', sc ->
        if n = n' then
          let (I.Dec (_, V')) = I.ctxDec (G, n) in
          eqSpineIL
            (GQ, D, D', ((S, s), (V', I.id)), ((S', s'), (V', I.id)), P', sc)
        else leftInstantiate (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P', sc)
    | GQ, D, D', UsVs, UsVs', P', sc ->
        if !Global.chatter > 4 then
          print
            (" Proved: "
            ^ atomicRCtxToString (G, Eq (UsVs, UsVs') :: D)
            ^ atomicRCtxToString (G, D')
            ^ " ---> "
            ^ atomicPredToString (G, P')
            ^ "\n")
        else ();
        true

  and eqSpineIL (GQ, D, D', (Ss, Vs), (Ss', Vs'), P', sc) =
    eqSpineILW (GQ, D, D', (Ss, Whnf.whnf Vs), (Ss', Whnf.whnf Vs'), P', sc)

  and eqSpineILW = function
    | GQ, D, D', ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), P', sc ->
        leftInstantiate (GQ, D, D', P', sc)
    | GQ, D, D', ((I.SClo (S, s'), s''), Vs), SsVs', P', sc ->
        eqSpineIL (GQ, D, D', ((S, I.comp (s', s'')), Vs), SsVs', P', sc)
    | GQ, D, D', SsVs, ((I.SClo (S', s'), s''), Vs'), P', sc ->
        eqSpineIL (GQ, D, D', SsVs, ((S', I.comp (s', s'')), Vs'), P', sc)
    | ( GQ,
        D,
        D',
        ((I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)),
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        P',
        sc ) ->
        let D1 = Eq (((U, s1), (V1, s2)), ((U', s1'), (V1', s2'))) :: D in
        eqSpineIL
          ( GQ,
            D1,
            D',
            ((S, s1), (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))),
            ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
            P',
            sc )

  and rightDecompose = function
    | GQ, D', Less (O, O') -> ordLtR (GQ, D', O, O')
    | GQ, D', Leq (O, O') -> ordLeR (GQ, D', O, O')
    | GQ, D', Eq (O, O') -> ordEqR (GQ, D', O, O')

  and ordLtR = function
    | GQ, D', R.Arg UsVs, R.Arg UsVs' ->
        ltAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
    | GQ, D', R.Lex O, R.Lex O' -> ltLexR (GQ, D', O, O')
    | GQ, D', R.Simul O, R.Simul O' -> ltSimulR (GQ, D', O, O')

  and ordLeR = function
    | GQ, D', R.Arg UsVs, R.Arg UsVs' ->
        leAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
    | GQ, D', R.Lex O, R.Lex O' ->
        ltLexR (GQ, D', O, O') || ordEqsR (GQ, D', O, O')
    | GQ, D', R.Simul O, R.Simul O' -> leSimulR (GQ, D', O, O')

  and ordEqR = function
    | GQ, D', R.Arg UsVs, R.Arg UsVs' ->
        conv (UsVs, UsVs')
        || eqAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
    | GQ, D', R.Lex O, R.Lex O' -> ordEqsR (GQ, D', O, O')
    | GQ, D', R.Simul O, R.Simul O' -> ordEqsR (GQ, D', O, O')

  and ordEqsR = function
    | GQ, D', [], [] -> true
    | GQ, D', O :: L, O' :: L' ->
        ordEqR (GQ, D', O, O') && ordEqsR (GQ, D', L, L')

  and ltLexR = function
    | GQ, D', [], [] -> false
    | GQ, D', O :: L, O' :: L' ->
        ordLtR (GQ, D', O, O')
        || (ordEqR (GQ, D', O, O') && ltLexR (GQ, D', L, L'))

  and leLexR (GQ, D', L, L') = ltLexR (GQ, D', L, L') || ordEqsR (GQ, D', L, L')

  and ltSimulR = function
    | GQ, D, [], [] -> false
    | GQ, D, O :: L, O' :: L' ->
        (ordLtR (GQ, D, O, O') && leSimulR (GQ, D, L, L'))
        || (ordEqR (GQ, D, O, O') && ltSimulR (GQ, D, L, L'))

  and leSimulR = function
    | GQ, D, [], [] -> true
    | GQ, D, O :: L, O' :: L' -> ordLeR (GQ, D, O, O') && leSimulR (GQ, D, L, L')

  and ltAtomicR (GQ, D, UsVs, UsVs', sc, k) =
    ltAtomicRW (GQ, D, Whnf.whnfEta UsVs, UsVs', sc, k)

  and ltAtomicRW = function
    | GQ, D, UsVs, UsVs', sc, k -> ltR (GQ, D, UsVs, UsVs', sc, k)
    | ( GQ,
        D,
        ((I.Lam (_, U), s1), (I.Pi ((Dec, _), V), s2)),
        ((U', s1'), (V', s2')),
        sc,
        k ) ->
        let UsVs' =
          ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift)))
        in
        let UsVs = ((U, I.dot1 s1), (V, I.dot1 s2)) in
        let D' = shiftACtx D (fun s -> I.comp (s, I.shift)) in
        ltAtomicR
          ( (I.Decl (G, N.decLUName (G, I.decSub (Dec, s2))), I.Decl (Q, All)),
            D',
            UsVs,
            UsVs',
            sc,
            k )

  and leAtomicR (GQ, D, UsVs, UsVs', sc, k) =
    leAtomicRW (GQ, D, Whnf.whnfEta UsVs, UsVs', sc, k)

  and leAtomicRW = function
    | GQ, D, UsVs, UsVs', sc, k -> leR (GQ, D, UsVs, UsVs', sc, k)
    | ( GQ,
        D,
        ((I.Lam (_, U), s1), (I.Pi ((Dec, _), V), s2)),
        ((U', s1'), (V', s2')),
        sc,
        k ) ->
        let D' = shiftACtx D (fun s -> I.comp (s, I.shift)) in
        let UsVs' =
          ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift)))
        in
        let UsVs = ((U, I.dot1 s1), (V, I.dot1 s2)) in
        leAtomicR
          ( (I.Decl (G, N.decLUName (G, I.decSub (Dec, s2))), I.Decl (Q, All)),
            D',
            UsVs,
            UsVs',
            sc,
            k )

  and eqAtomicR (GQ, D, UsVs, UsVs', sc, k) =
    eqAtomicRW (GQ, D, Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', sc, k)

  and eqAtomicRW = function
    | ( GQ,
        D,
        ((I.Lam (_, U), s1), (I.Pi ((Dec, _), V), s2)),
        ((I.Lam (_, U'), s1'), (I.Pi ((Dec', _), V'), s2')),
        sc,
        k ) ->
        eqAtomicR
          ( (I.Decl (G, N.decLUName (G, I.decSub (Dec, s2))), I.Decl (Q, All)),
            shiftACtx D (fun s -> I.comp (s, I.shift)),
            ((U, I.dot1 s1'), (V, I.dot1 s2')),
            ((U', I.dot1 s1'), (V', I.dot1 s2')),
            sc,
            k )
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        eqR (GQ, D, (Us, Vs), (Us', Vs'), sc, k)
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k -> false

  and ltR (GQ, D, UsVs, UsVs', sc, k) =
    ltRW (GQ, D, UsVs, Whnf.whnfEta UsVs', sc, k)

  and ltRW = function
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us') then
          k (GQ, D, [], Less ((Us, Vs), (Us', Vs')), sc)
          (* either leftInstantiate D or  atomic reasoning *)
        else ltSpineR (GQ, D, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, k)
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us') then
          k (GQ, D, [], Less ((Us, Vs), (Us', Vs')), sc)
          (* either leftInstantiate D or  atomic reasoning *)
        else ltSpineR (GQ, D, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, k)
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us') then
          k (GQ, D, [], Less ((Us, Vs), (Us', Vs')), sc)
          (* either leftInstantiate D or  atomic reasoning *)
        else
          let (I.Dec (_, V')) = I.ctxDec (G, n) in
          ltSpineR (GQ, D, (Us, Vs), ((S', s'), (V', I.id)), sc, k)
    | GQ, D, _, ((I.EVar _, _), _), _, _ -> false
    | ( GQ,
        D,
        ((U, s1), (V, s2)),
        ( (I.Lam (I.Dec (_, V1'), U'), s1'),
          (I.Pi ((I.Dec (_, V2'), _), V'), s2') ),
        sc,
        k ) ->
        if
          Subordinate.equiv (I.targetFam V, I.targetFam V1')
          (* == I.targetFam V2' *)
        then
          (* enforce that X is only instantiated to parameters *)
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' =
           fun () ->
            isParameter (Q, X);
            sc ()
          in
          ltR
            ( GQ,
              D,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc',
              k )
        else if Subordinate.below (I.targetFam V1', I.targetFam V) then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          ltR
            ( GQ,
              D,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc,
              k )
        else false

  and ltSpineR (GQ, D, (Us, Vs), (Ss', Vs'), sc, k) =
    ltSpineRW (GQ, D, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, k)

  and ltSpineRW = function
    | GQ, D, (Us, Vs), ((I.Nil, _), _), _, _ -> false
    | GQ, D, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, k ->
        ltSpineR (GQ, D, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, k)
    | ( GQ,
        D,
        (Us, Vs),
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        sc,
        k ) ->
        leAtomicR (GQ, D, (Us, Vs), ((U', s1'), (V1', s2')), sc, k)
        || ltSpineR
             ( GQ,
               D,
               (Us, Vs),
               ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
               sc,
               k )

  and leR (GQ, D, UsVs, UsVs', sc, k) =
    leRW (GQ, D, UsVs, Whnf.whnfEta UsVs', sc, k)

  and leRW = function
    | ( GQ,
        D,
        ((U, s1), (V, s2)),
        ( (I.Lam (I.Dec (_, V1'), U'), s1'),
          (I.Pi ((I.Dec (_, V2'), _), V'), s2') ),
        sc,
        k ) ->
        if
          Subordinate.equiv (I.targetFam V, I.targetFam V1')
          (* == I.targetFam V2' *)
        then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          (* enforces that X can only bound to parameter or remain uninstantiated *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          let sc' = fun () -> isParameter (Q, X) && sc () in
          leR
            ( GQ,
              D,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc',
              k )
        else if Subordinate.below (I.targetFam V1', I.targetFam V) then
          (* = I.newEVar (I.EClo (V2', s2')) *)
          let X = I.newEVar (G, I.EClo (V1', s1')) in
          leR
            ( GQ,
              D,
              ((U, s1), (V, s2)),
              ((U', I.Dot (I.Exp X, s1')), (V', I.Dot (I.Exp X, s2'))),
              sc,
              k )
        else false
    | GQ, D, UsVs, UsVs', sc, k ->
        ltR (GQ, D, UsVs, UsVs', sc, k) || eqR (GQ, D, UsVs, UsVs', sc, k)

  and eqR (GQ, D, UsVs, UsVs', sc, k) =
    Cs.CSManager.trail (fun () -> eq (G, UsVs, UsVs') && sc ())
    || eqR' (GQ, D, UsVs, UsVs', sc, k)

  and eqR' = function
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k -> false
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k -> false
    | GQ, D, UsVs, UsVs', sc, k ->
        if eqCid (c, c') then
          eqSpineR
            ( GQ,
              D,
              ((S, s), (I.constType c, I.id)),
              ((S', s'), (I.constType c', I.id)),
              sc,
              k )
        else false
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us') then k (GQ, D, [], Eq ((Us', Vs'), (Us, Vs)), sc)
          (* either leftInstantiate D or atomic reasoning *)
        else false
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us) then k (GQ, D, [], Eq ((Us, Vs), (Us', Vs')), sc)
          (* either leftInstantiate D or atomic reasoning *)
        else false
    | GQ, D, UsVs, UsVs', sc, k ->
        if eqCid (c, c') then
          eqSpineR
            ( GQ,
              D,
              ((S, s), (I.constType c, I.id)),
              ((S', s'), (I.constType c', I.id)),
              sc,
              k )
        else false
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us') then k (GQ, D, [], Eq ((Us', Vs'), (Us, Vs)), sc)
          (* either leftInstantiate D or atomic reasoning *)
        else false
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if isAtomic (GQ, Us) then k (GQ, D, [], Eq ((Us, Vs), (Us', Vs')), sc)
          (* either leftInstantiate D or atomic reasoning *)
        else false
    | GQ, D, (Us, Vs), (Us', Vs'), sc, k ->
        if n = n' then
          let (I.Dec (_, V')) = I.ctxDec (G, n) in
          eqSpineR (GQ, D, ((S, s), (V', I.id)), ((S', s'), (V', I.id)), sc, k)
        else k (GQ, D, [], Eq ((Us, Vs), (Us', Vs')), sc)
    | GQ, D, UsVs, UsVs', sc, k -> k (GQ, D, [], Eq (UsVs, UsVs'), sc)

  and eqSpineR (GQ, D, (Ss, Vs), (Ss', Vs'), sc, k) =
    eqSpineRW (GQ, D, (Ss, Whnf.whnf Vs), (Ss', Whnf.whnf Vs'), sc, k)

  and eqSpineRW = function
    | GQ, D, ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), sc, k -> true
    | GQ, D, ((I.SClo (S, s'), s''), Vs), SsVs', sc, k ->
        eqSpineR (GQ, D, ((S, I.comp (s', s'')), Vs), SsVs', sc, k)
    | GQ, D, SsVs, ((I.SClo (S', s'), s''), Vs'), sc, k ->
        eqSpineR (GQ, D, SsVs, ((S', I.comp (s', s'')), Vs'), sc, k)
    | ( GQ,
        D,
        ((I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)),
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        sc,
        k ) ->
        eqAtomicR (GQ, D, ((U, s1), (V1, s2)), ((U', s1'), (V1', s2')), sc, k)
        && eqSpineR
             ( GQ,
               D,
               ((S, s1), (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))),
               ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
               sc,
               k )
    | GQ, D, SsVs, SsVs', sc, k -> false
  (*--------------------------------------------------------------*)

  (* leftDecompose (G, Q, D, D', P) = B

      if G : Q and
         D --> P  where D might contain orders (lex and simul)

      then D' --> P
           where all orders in D' are atomic

      D' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < L

      L := Root(c, Nil) | Root(n, Nil)
      R := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)


      Eq : R = L
      R := Root(n, Nil) | Lam(x:A, R)
      L := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)

    *)

  let rec leftDecompose = function
    | GQ, [], D', P -> rightDecompose (GQ, D', P)
    | GQ, Less (R.Arg UsVs, R.Arg UsVs') :: D, D', P ->
        ltAtomicL (GQ, D, D', UsVs, UsVs', P)
    | GQ, Less (R.Lex O, R.Lex O') :: D, D', P -> ltLexL (GQ, D, D', O, O', P)
    | GQ, Less (R.Simul O, R.Simul O') :: D, D', P ->
        ltSimulL (GQ, D, D', O, O', P)
    | GQ, Leq (R.Arg UsVs, R.Arg UsVs') :: D, D', P ->
        leAtomicL (GQ, D, D', UsVs, UsVs', P)
    | GQ, Leq (R.Lex O, R.Lex O') :: D, D', P ->
        leftDecompose (GQ, Less (R.Lex O, R.Lex O') :: D, D', P)
        && leftDecompose (GQ, Eq (R.Lex O, R.Lex O') :: D, D', P)
    | GQ, Leq (R.Simul O, R.Simul O') :: D, D', P ->
        leSimulL (GQ, D, D', O, O', P)
    | GQ, Eq (R.Arg UsVs, R.Arg UsVs') :: D, D', P ->
        eqAtomicL (GQ, D, D', UsVs, UsVs', P)
    | GQ, Eq (R.Lex O, R.Lex O') :: D, D', P -> eqsL (GQ, D, D', O, O', P)
    | GQ, Eq (R.Simul O, R.Simul O') :: D, D', P -> eqsL (GQ, D, D', O, O', P)
    | GQ, Pi (Dec, O) :: D, D', P ->
        if !Global.chatter > 3 then (
          print " Ignoring quantified order ";
          print (F.makestring_fmt (fmtPredicate (G, Pi (Dec, O)))))
        else ();
        leftDecompose (GQ, D, D', P)

  and ltLexL = function
    | GQ, D, D', [], [], P -> true
    | GQ, D, D', O :: L, O' :: L', P ->
        leftDecompose (GQ, Less (O, O') :: D, D', P)
        && ltLexL (GQ, Eq (O, O') :: D, D', L, L', P)

  and eqsL = function
    | GQ, D, D', [], [], P -> true
    | GQ, D, D', O :: L, O' :: L', P ->
        leftDecompose (GQ, Eq (O, O') :: D, D', P) && eqsL (GQ, D, D', L, L', P)

  and ltSimulL = function
    | GQ, D, D', [], [], P -> leftDecompose (GQ, D, D', P)
    | GQ, D, D', O :: L, O' :: L', P ->
        leSimulL (GQ, Less (O, O') :: D, D', L, L', P)
        || ltSimulL (GQ, Eq (O, O') :: D, D', L, L', P)

  and leSimulL = function
    | GQ, D, D', [], [], P -> leftDecompose (GQ, D, D', P)
    | GQ, D, D', O :: L, O' :: L', P ->
        leSimulL (GQ, Leq (O, O') :: D, D', L, L', P)

  and ltAtomicL (GQ, D, D', UsVs, UsVs', P) =
    ltAtomicLW (GQ, D, D', UsVs, Whnf.whnfEta UsVs', P)

  and ltAtomicLW = function
    | GQ, D, D', UsVs, (Us', Vs'), P -> ltL (GQ, D, D', UsVs, (Us', Vs'), P)
    | ( GQ,
        D,
        D',
        ((U, s1), (V, s2)),
        ((I.Lam (_, U'), s1'), (I.Pi ((Dec', _), V'), s2')),
        P ) ->
        let D1 = shiftRCtx D (fun s -> I.comp (s, I.shift)) in
        let D1' = shiftACtx D' (fun s -> I.comp (s, I.shift)) in
        let UsVs = ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift))) in
        let UsVs' = ((U', I.dot1 s1'), (V', I.dot1 s2')) in
        let P' = shiftP P (fun s -> I.comp (s, I.shift)) in
        ltAtomicL
          ( (I.Decl (G, N.decLUName (G, I.decSub (Dec', s2'))), I.Decl (Q, All)),
            D1,
            D1',
            UsVs,
            UsVs',
            P' )

  and leAtomicL (GQ, D, D', UsVs, UsVs', P) =
    leAtomicLW (GQ, D, D', UsVs, Whnf.whnfEta UsVs', P)

  and leAtomicLW = function
    | GQ, D, D', UsVs, (Us', Vs'), P -> leL (GQ, D, D', UsVs, (Us', Vs'), P)
    | ( GQ,
        D,
        D',
        ((U, s1), (V, s2)),
        ((I.Lam (_, U'), s1'), (I.Pi ((Dec', _), V'), s2')),
        P ) ->
        let D1 = shiftRCtx D (fun s -> I.comp (s, I.shift)) in
        let D1' = shiftACtx D' (fun s -> I.comp (s, I.shift)) in
        let UsVs = ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift))) in
        let UsVs' = ((U', I.dot1 s1'), (V', I.dot1 s2')) in
        let P' = shiftP P (fun s -> I.comp (s, I.shift)) in
        leAtomicL
          ( (I.Decl (G, N.decLUName (G, I.decSub (Dec', s2'))), I.Decl (Q, All)),
            D1,
            D1',
            UsVs,
            UsVs',
            P' )

  and eqAtomicL (GQ, D, D', UsVs, UsVs', P) =
    eqAtomicLW (GQ, D, D', Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P)

  and eqAtomicLW = function
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        eqL (GQ, D, D', (Us, Vs), (Us', Vs'), P)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P -> true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P -> true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        leftDecompose (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P)

  and leL (GQ, D, D', UsVs, UsVs', P) =
    ltAtomicL (GQ, D, D', UsVs, UsVs', P)
    && eqAtomicL (GQ, D, D', UsVs, UsVs', P)

  and ltL (GQ, D, D', UsVs, (Us', Vs'), P) =
    ltLW (GQ, D, D', UsVs, (Whnf.whnf Us', Vs'), P)

  and ltLW = function
    | GQ, D, D', UsVs, (Us', Vs'), P ->
        if isAtomic (GQ, Us') then
          leftDecompose (GQ, D, Less (UsVs, (Us', Vs')) :: D', P)
        else
          let (I.Dec (_, V')) = I.ctxDec (G, n) in
          ltSpineL (GQ, D, D', UsVs, ((S', s'), (V', I.id)), P)
    | GQ, D, D', UsVs, ((I.Root (I.Const c, S'), s'), Vs'), P ->
        ltSpineL (GQ, D, D', UsVs, ((S', s'), (I.constType c, I.id)), P)
    | GQ, D, D', UsVs, ((I.Root (I.Def c, S'), s'), Vs'), P ->
        ltSpineL (GQ, D, D', UsVs, ((S', s'), (I.constType c, I.id)), P)

  and ltSpineL (GQ, D, D', UsVs, (Ss', Vs'), P) =
    ltSpineLW (GQ, D, D', UsVs, (Ss', Whnf.whnf Vs'), P)

  and ltSpineLW = function
    | GQ, D, D', UsVs, ((I.Nil, _), _), _ -> true
    | GQ, D, D', UsVs, ((I.SClo (S, s'), s''), Vs'), P ->
        ltSpineL (GQ, D, D', UsVs, ((S, I.comp (s', s'')), Vs'), P)
    | ( GQ,
        D,
        D',
        UsVs,
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        P ) ->
        leAtomicL (GQ, D, D', UsVs, ((U', s1'), (V1', s2')), P)
        && ltSpineL
             ( GQ,
               D,
               D',
               UsVs,
               ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
               P )

  and eqL (GQ, D, D', UsVs, UsVs', P) =
    eqLW (GQ, D, D', Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P)

  and eqLW = function
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        leftDecompose (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P)
    | GQ, D, D', (Us, Vs), (Us', Vs'), P -> true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P -> true
    | GQ, D, D', UsVs, UsVs', P ->
        if eqCid (c, c') then
          eqSpineL
            ( GQ,
              D,
              D',
              ((S, s), (I.constType c, I.id)),
              ((S', s'), (I.constType c', I.id)),
              P )
        else true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        if isAtomic (GQ, Us') then
          leftDecompose (GQ, D, Eq ((Us', Vs'), (Us, Vs)) :: D', P)
        else true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        if isAtomic (GQ, Us) then
          leftDecompose (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P)
        else true
    | GQ, D, D', UsVs, UsVs', P ->
        if eqCid (c, c') then
          eqSpineL
            ( GQ,
              D,
              D',
              ((S, s), (I.constType c, I.id)),
              ((S', s'), (I.constType c', I.id)),
              P )
        else true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        if isAtomic (GQ, Us') then
          leftDecompose (GQ, D, Eq ((Us', Vs'), (Us, Vs)) :: D', P)
        else true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        if isAtomic (GQ, Us) then
          leftDecompose (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P)
        else true
    | GQ, D, D', (Us, Vs), (Us', Vs'), P ->
        if n = n' then
          let (I.Dec (_, V')) = I.ctxDec (G, n) in
          eqSpineL (GQ, D, D', ((S, s), (V', I.id)), ((S', s'), (V', I.id)), P)
        else leftDecompose (GQ, D, Eq ((Us, Vs), (Us', Vs')) :: D', P)
    | GQ, D, D', UsVs, UsVs', P ->
        leftDecompose (GQ, D, Eq (UsVs, UsVs') :: D', P)

  and eqSpineL (GQ, D, D', (Ss, Vs), (Ss', Vs'), P) =
    eqSpineLW (GQ, D, D', (Ss, Whnf.whnf Vs), (Ss', Whnf.whnf Vs'), P)

  and eqSpineLW = function
    | GQ, D, D', ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), P ->
        leftDecompose (GQ, D, D', P)
    | GQ, D, D', ((I.SClo (S, s'), s''), Vs), SsVs', P ->
        eqSpineL (GQ, D, D', ((S, I.comp (s', s'')), Vs), SsVs', P)
    | GQ, D, D', SsVs, ((I.SClo (S', s'), s''), Vs'), P ->
        eqSpineL (GQ, D, D', SsVs, ((S', I.comp (s', s'')), Vs'), P)
    | ( GQ,
        D,
        D',
        ((I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)),
        ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
        P ) ->
        let D1 =
          Eq (R.Arg ((U, s1), (V1, s2)), R.Arg ((U', s1'), (V1', s2'))) :: D
        in
        eqSpineL
          ( GQ,
            D1,
            D',
            ((S, s1), (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))),
            ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
            P )
  (*--------------------------------------------------------------*)

  (* Infer: D --> P *)

  (* deduce (G, Q, D, P) = B

      B iff
         G :  Q
     and G |- D
     and G |- P
     and D implies P
    *)

  let rec deduce (G, Q, D, P) = leftDecompose ((G, Q), D, [], P)
  let deduce = deduce
  let shiftRCtx = shiftRCtx
  let shiftPred = shiftP
  (* local *)
end

(* functor checking  *)
