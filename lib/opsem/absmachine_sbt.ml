(* Abstract Machine using substitution trees *)

(* Author: Iliano Cervesato *)

(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

module AbsMachineSbt
    (Unify : UNIFY)
    (SubTree : SUBTREE)
    (Assign : ASSIGN)
    (Index : INDEX)
    (CPrint : CPRINT)
    (Print : PRINT)
    (Names : NAMES) : ABSMACHINESBT = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure CompSyn = CompSyn' !*)

  module I = IntSyn
  module C = CompSyn

  let mSig :
      (IntSyn.exp * IntSyn.sub)
      * CompSyn.dProg
      * (CompSyn.flatterm list -> unit) ->
      unit ref =
    ref (fun (ps, dp, sc) -> ())
  (* We write
       G |- M : g
     if M is a canonical proof term for_sml goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for_sml residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)

  let rec cidFromHead = function I.Const a -> a | I.Def a -> a

  let rec eqHead = function
    | I.Const a, I.Const a' -> a = a'
    | I.Def a, I.Def a' -> a = a'
    | _ -> false
  (* Wed Mar 13 10:27:00 2002 -bp  *)

  (* should probably go to intsyn.fun *)

  let rec compose' = function
    | IntSyn.Null, G -> G
    | IntSyn.Decl (G, D), G' -> IntSyn.Decl (compose' (G, G'), D)

  let rec shift = function
    | IntSyn.Null, s -> s
    | IntSyn.Decl (G, D), s -> I.dot1 (shift (G, s))

  let rec invShiftN (n, s) =
    if n = 0 then I.comp (I.invShift, s)
    else I.comp (I.invShift, invShiftN (n - 1, s))

  let rec raiseType = function
    | I.Null, V -> V
    | I.Decl (G, D), V -> raiseType (G, I.Pi ((D, I.Maybe), V))

  let rec printSub = function
    | IntSyn.Shift n -> print ("Shift " ^ Int.toString n ^ "\n")
    | IntSyn.Dot (IntSyn.Idx n, s) ->
        print ("Idx " ^ Int.toString n ^ " . ");
        printSub s
    | IntSyn.Dot (IntSyn.Exp (IntSyn.EVar (_, _, _, _)), s) ->
        print "Exp (EVar _ ). ";
        printSub s
    | IntSyn.Dot (IntSyn.Exp (IntSyn.AVar _), s) ->
        print "Exp (AVar _ ). ";
        printSub s
    | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (IntSyn.AVar _, _)), s) ->
        print "Exp (AVar _ ). ";
        printSub s
    | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (_, _)), s) ->
        print "Exp (EClo _ ). ";
        printSub s
    | IntSyn.Dot (IntSyn.Exp _, s) ->
        print "Exp (_ ). ";
        printSub s
    | IntSyn.Dot (IntSyn.Undef, s) ->
        print "Undef . ";
        printSub s
  (* ctxToEVarSub D = s*)

  let rec ctxToEVarSub = function
    | Gglobal, I.Null, s -> s
    | Gglobal, I.Decl (G, I.Dec (_, A)), s ->
        let s' = ctxToEVarSub (Gglobal, G, s) in
        let X = I.newEVar (Gglobal, I.EClo (A, s')) in
        I.Dot (I.Exp X, s')
    | Gglobal, I.Decl (G, I.ADec (_, d)), s ->
        let X = I.newAVar () in
        I.Dot (I.Exp (I.EClo (X, I.Shift ~-d)), ctxToEVarSub (Gglobal, G, s))
  (* solve' ((g, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)

  let rec solve' = function
    | (C.Atom p, s), dp, sc -> matchAtom ((p, s), dp, sc)
    | (C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc ->
        let D' = I.Dec (None, I.EClo (A, s)) in
        solve'
          ( (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
            sc )
    | (C.All (D, g), s), C.DProg (G, dPool), sc ->
        let D' = Names.decLUName (G, I.decSub (D, s)) in
        solve'
          ( (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
            sc )

  and rSolve = function
    | ps', (C.Eq Q, s), C.DProg (G, dPool), sc ->
        if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *) then
          sc [] (* call success continuation *)
        else ()
    | ps', (C.Assign (Q, eqns), s), dp, sc -> (
        match Assign.assignable (G, ps', (Q, s)) with
        | Some cnstr -> aSolve ((eqns, s), dp, cnstr, fun () -> sc [])
        | None -> ())
    | ps', (C.And (r, A, g), s), dp, sc ->
        (* is this EVar redundant? -fp *)
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            fun skel1 -> solve' ((g, s), dp, fun skel2 -> sc (skel1 @ skel2)) )
    | ps', (C.Exists (I.Dec (_, A), r), s), dp, sc ->
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve (ps', (r, I.Dot (I.Exp X, s)), dp, sc)
    | ps', (C.Axists (I.ADec (_, d), r), s), dp, sc ->
        let X' = I.newAVar () in
        rSolve (ps', (r, I.Dot (I.Exp (I.EClo (X', I.Shift ~-d)), s)), dp, sc)
  (* we don't increase the proof term here! *)

  and aSolve = function
    | (C.Trivial, s), dp, cnstr, sc ->
        if Assign.solveCnstr cnstr then sc () else () (* Fail *)
    | (C.UnifyEq (G', e1, N, eqns), s), dp, cnstr, sc ->
        let G'' = compose' (G', G) in
        let s' = shift (G', s) in
        if Assign.unifiable (G'', (N, s'), (e1, s')) then
          aSolve ((eqns, s), dp, cnstr, sc)
        else () (* Fail *)

  and sSolve = function
    | (C.True, s), dp, sc -> sc []
    | (C.Conjunct (g, A, Sgoals), s), dp, sc ->
        solve'
          ( (g, s),
            dp,
            fun skel1 ->
              sSolve ((Sgoals, s), dp, fun skel2 -> sc (skel1 @ skel2)) )

  and matchSig (ps', dp, sc) =
    let rec mSig = function
      | [] -> ()
      | Hc :: sgn' ->
          let (C.SClause r) = C.sProgLookup (cidFromHead Hc) in
          (* trail to undo EVar instantiations *)
          CSManager.trail (fun () ->
              rSolve (ps', (r, I.id), dp, fun S -> sc (C.Pc c :: S)));
          mSig sgn'
    in
    mSig (Index.lookup (cidFromHead Ha))

  and matchIndexSig (ps', dp, sc) =
    SubTree.matchSig
      ( cidFromHead Ha,
        G,
        ps',
        fun ((ConjGoals, s), clauseName) ->
          sSolve ((ConjGoals, s), dp, fun S -> sc (C.Pc clauseName :: S)) )

  and matchAtom (ps', dp, sc) =
    (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for_sml solving atomic goal ps', starting
           with the most recent one.
        *)
    let rec matchDProg = function
      | I.Null, _ -> !mSig (ps', dp, sc)
      | I.Decl (dPool', C.Dec (r, s, Ha')), k ->
          if eqHead (Ha, Ha') then (
            CSManager.trail (* trail to undo EVar instantiations *) (fun () ->
                rSolve
                  ( ps',
                    (r, I.comp (s, I.Shift k)),
                    dp,
                    fun S -> sc (C.Dc k :: S) ));
            matchDProg (dPool', k + 1))
          else matchDProg (dPool', k + 1)
      | I.Decl (dPool', C.Parameter), k -> matchDProg (dPool', k + 1)
    in
    let rec matchConstraint (solve, try_) =
      let succeeded =
        CSManager.trail (fun () ->
            match solve (G, I.SClo (S, s), try_) with
            | Some U ->
                sc [ C.Csolver U ];
                true
            | None -> false)
      in
      if succeeded then matchConstraint (solve, try_ + 1) else ()
    in
    match I.constStatus (cidFromHead Ha) with
    | I.Constraint (cs, solve) -> matchConstraint (solve, 0)
    | _ -> matchDProg (dPool, 1)

  let rec solve args =
    match !CompSyn.optimize with
    | CompSyn.No ->
        mSig := matchSig;
        solve' args
    | CompSyn.LinearHeads ->
        mSig := matchSig;
        solve' args
    | CompSyn.Indexing ->
        mSig := matchIndexSig;
        solve' args
  (* local ... *)
end

(* functor AbsMachineSbt *)
(* Abstract Machine *)

(* Author: Iliano Cervesato *)

(* Modified: Jeff Polakow *)

(* Modified: Frank Pfenning *)

module type ABSMACHINESBT = sig
  (*! structure IntSyn  : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val solve :
    (CompSyn.goal * IntSyn.sub)
    * CompSyn.dProg
    * (CompSyn.flatterm list -> unit) ->
    unit
end

(* signature ABSMACHINESBT *)
