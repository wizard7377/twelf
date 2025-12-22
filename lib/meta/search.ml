(* Search (based on abstract machine ) : Version 1.3 *)

(* Author: Carsten Schuermann *)

module MTPSearch
    (Global : GLOBAL)
    (Abstract : ABSTRACT)
    (MTPGlobal : MTPGLOBAL)
    (StateSyn' : STATESYN)
    (Whnf : WHNF)
    (Unify : UNIFY)
    (Assign : ASSIGN)
    (Index : INDEX)
    (Compile : COMPILE)
    (CPrint : CPRINT)
    (Print : PRINT)
    (Names : NAMES) : MTPSEARCH = struct
  (*! structure IntSyn = IntSyn' !*)

  module StateSyn = StateSyn'
  (*! structure CompSyn = CompSyn' !*)

  exception Error of string

  module I = IntSyn
  module C = CompSyn
  (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)

  let rec isInstantiated = function
    | I.Root (I.Const cid, _) -> true
    | I.Pi (_, V) -> isInstantiated V
    | I.Root (I.Def cid, _) -> true
    | I.Redex (V, S) -> isInstantiated V
    | I.Lam (_, V) -> isInstantiated V
    | I.EVar ({ contents = Some V }, _, _, _) -> isInstantiated V
    | I.EClo (V, s) -> isInstantiated V
    | _ -> false

  let rec compose' = function
    | IntSyn.Null, G -> G
    | IntSyn.Decl (G, D), G' -> IntSyn.Decl (compose' (G, G'), D)

  let rec shift = function
    | IntSyn.Null, s -> s
    | IntSyn.Decl (G, D), s -> I.dot1 (shift (G, s))
  (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)

  let rec raiseType = function
    | I.Null, V -> V
    | I.Decl (G, D), V -> raiseType (G, I.Pi ((D, I.Maybe), V))
  (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)

  let rec exists P K =
    let rec exists' = function
      | I.Null -> false
      | I.Decl (K', Y) -> P Y || exists' K'
    in
    exists' K
  (* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)

  let rec occursInExp (r, Vs) = occursInExpW (r, Whnf.whnf Vs)

  and occursInExpW = function
    | r, (I.Uni _, _) -> false
    | r, (I.Pi ((D, _), V), s) ->
        occursInDec (r, (D, s)) || occursInExp (r, (V, I.dot1 s))
    | r, (I.Root (_, S), s) -> occursInSpine (r, (S, s))
    | r, (I.Lam (D, V), s) ->
        occursInDec (r, (D, s)) || occursInExp (r, (V, I.dot1 s))
    | r, (I.EVar (r', _, V', _), s) -> r = r' || occursInExp (r, (V', s))
    | r, (I.FgnExp csfe, s) ->
        I.FgnExpStd.fold csfe (fun (U, B) -> B || occursInExp (r, (U, s))) false

  and occursInSpine = function
    | _, (I.Nil, _) -> false
    | r, (I.SClo (S, s'), s) -> occursInSpine (r, (S, I.comp (s', s)))
    | r, (I.App (U, S), s) ->
        occursInExp (r, (U, s)) || occursInSpine (r, (S, s))

  and occursInDec (r, (I.Dec (_, V), s)) = occursInExp (r, (V, s))
  (* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)

  let rec nonIndex = function
    | _, [] -> true
    | r, I.EVar (_, _, V, _) :: GE ->
        (not (occursInExp (r, (V, I.id)))) && nonIndex (r, GE)
  (* select (GE, (V, s), acc) = acc'

       Invariant:
    *)

  (* Efficiency: repeated whnf for_sml every subterm in Vs!!! *)

  let rec selectEVar = function
    | [] -> []
    | X :: GE ->
        let Xs = selectEVar GE in
        if nonIndex (r, Xs) then Xs @ [ X ] else Xs
    | X :: GE ->
        let Xs = selectEVar GE in
        if nonIndex (r, Xs) then X :: Xs else Xs
  (* pruneCtx (G, n) = G'

       Invariant:
       If   |- G ctx
       and  G = G0, G1
       and  |G1| = n
       then |- G' = G0 ctx
    *)

  let rec pruneCtx = function
    | G, 0 -> G
    | I.Decl (G, _), n -> pruneCtx (G, n - 1)

  let rec cidFromHead = function
    | I.Const a -> a
    | I.Def a -> a
    | I.Skonst a -> a
  (* only used for_sml type families of compiled clauses *)

  let rec eqHead = function
    | I.Const a, I.Const a' -> a = a'
    | I.Def a, I.Def a' -> a = a'
    | _ -> false
  (* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for_sml iterative deepening,
            used in the universal case for_sml max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)

  let rec solve = function
    | max, depth, (C.Atom p, s), dp, sc -> matchAtom (max, depth, (p, s), dp, sc)
    | max, depth, (C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc ->
        let D' = I.Dec (None, I.EClo (A, s)) in
        solve
          ( max,
            depth + 1,
            (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
            fun M -> sc (I.Lam (D', M)) )
    | max, depth, (C.All (D, g), s), C.DProg (G, dPool), sc ->
        let D' = I.decSub (D, s) in
        solve
          ( max,
            depth + 1,
            (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
            fun M -> sc (I.Lam (D', M)) )

  and rSolve = function
    | max, depth, ps', (C.Eq Q, s), C.DProg (G, dPool), sc ->
        if Unify.unifiable (G, ps', (Q, s)) then sc I.Nil else ()
    | max, depth, ps', (C.Assign (Q, eqns), s), dp, sc -> (
        match Assign.assignable (G, ps', (Q, s)) with
        | Some cnstr -> aSolve ((eqns, s), dp, cnstr, fun () -> sc I.Nil)
        | None -> ())
    | max, depth, ps', (C.And (r, A, g), s), dp, sc ->
        (* is this EVar redundant? -fp *)
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( max,
            depth,
            ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            fun S -> solve (max, depth, (g, s), dp, fun M -> sc (I.App (M, S)))
          )
    | max, depth, ps', (C.In (r, A, g), s), dp, sc ->
        (* G |- g goal *)
        (* G |- A : type *)
        (* G, A |- r resgoal *)
        (* G0, Gl  |- s : G *)
        (* G0, Gl  |- w : G0 *)
        (* G0 |- iw : G0, Gl *)
        (* G0 |- w : G *)
        (* G0 |- X : A[s'] *)
        (* G0, Gl |- X' : A[s'][w] = A[s] *)
        let G0 = pruneCtx (G, depth) in
        let dPool0 = pruneCtx (dPool, depth) in
        let w = I.Shift depth in
        let iw = Whnf.invert w in
        let s' = I.comp (s, iw) in
        let X = I.newEVar (G0, I.EClo (A, s')) in
        let X' = I.EClo (X, w) in
        rSolve
          ( max,
            depth,
            ps',
            (r, I.Dot (I.Exp X', s)),
            dp,
            fun S ->
              if isInstantiated X then sc (I.App (X', S))
              else
                solve
                  ( max,
                    0,
                    (g, s'),
                    C.DProg (G0, dPool0),
                    fun M ->
                      try
                        Unify.unify (G0, (X, I.id), (M, I.id));
                        sc (I.App (I.EClo (M, w), S))
                      with Unify.Unify _ -> () ) )
    | max, depth, ps', (C.Exists (I.Dec (_, A), r), s), dp, sc ->
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( max,
            depth,
            ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            fun S -> sc (I.App (X, S)) )
    | max, depth, ps', (C.Axists (I.ADec (Some X, d), r), s), dp, sc ->
        let X' = I.newAVar () in
        rSolve
          ( max,
            depth,
            ps',
            (r, I.Dot (I.Exp (I.EClo (X', I.Shift ~-d)), s)),
            dp,
            sc )
  (* we don't increase the proof term here! *)

  and aSolve = function
    | (C.Trivial, s), dp, cnstr, sc ->
        if Assign.solveCnstr cnstr then sc () else ()
    | (C.UnifyEq (G', e1, N, eqns), s), dp, cnstr, sc ->
        let G'' = compose' (G', G) in
        let s' = shift (G', s) in
        if Assign.unifiable (G'', (N, s'), (e1, s')) then
          aSolve ((eqns, s), dp, cnstr, sc)
        else ()

  and matchAtom = function
    | 0, _, _, _, _ -> ()
    | max, depth, ps', dp, sc ->
        let rec matchSig' = function
          | [] -> ()
          | Hc :: sgn' ->
              let (C.SClause r) = C.sProgLookup (cidFromHead Hc) in
              let _ =
                CSManager.trail (fun () ->
                    rSolve
                      ( max - 1,
                        depth,
                        ps',
                        (r, I.id),
                        dp,
                        fun S -> sc (I.Root (Hc, S)) ))
              in
              matchSig' sgn'
        in
        let rec matchDProg = function
          | I.Null, _ -> matchSig' (Index.lookup (cidFromHead Ha))
          | I.Decl (dPool', C.Dec (r, s, Ha')), n ->
              if eqHead (Ha, Ha') then
                let _ =
                  CSManager.trail (fun () ->
                      rSolve
                        ( max - 1,
                          depth,
                          ps',
                          (r, I.comp (s, I.Shift n)),
                          dp,
                          fun S -> sc (I.Root (I.BVar n, S)) ))
                in
                matchDProg (dPool', n + 1)
              else matchDProg (dPool', n + 1)
          | I.Decl (dPool', C.Parameter), n -> matchDProg (dPool', n + 1)
        in
        matchDProg (dPool, 1)

  and searchEx' = function
    | max, ([], sc) -> sc max
    | max, (X :: GE, sc) ->
        solve
          ( max,
            0,
            (Compile.compileGoal (G, V), I.id),
            Compile.compileCtx false G,
            fun U' ->
              try
                Unify.unify (G, (X, I.id), (U', I.id));
                searchEx' max (GE, sc)
              with Unify.Unify _ -> () )
  (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MTPGlobal.maxLevel
    *)

  let rec deepen depth f P =
    let rec deepen' level =
      if level > depth then ()
      else (
        if !Global.chatter > 5 then print "#" else ();
        f level P;
        deepen' (level + 1))
    in
    deepen' 1
  (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list containing the one result from executing the success continuation
         All EVar's got instantiated with the smallest possible terms.
    *)

  let rec searchEx (it, depth) (GE, sc) =
    if !Global.chatter > 5 then print "[Search: " else ();
    deepen depth searchEx'
      ( selectEVar GE,
        fun max ->
          if !Global.chatter > 5 then print "OK]\n" else ();
          let GE' =
            foldr (fun (X, L) -> Abstract.collectEVars (G, (X, I.id), L)) [] GE
          in
          let gE' = List.length GE' in
          if gE' > 0 then if it > 0 then searchEx (it - 1, 1) (GE', sc) else ()
          else sc max
        (* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *)
      );
    if !Global.chatter > 5 then print "FAIL]\n" else ();
    ()
  (* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit

       Side effect:
       success continuation will raise exception
    *)

  (* Shared contexts of EVars in GE may recompiled many times *)

  let rec search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc)
  let searchEx = search
  (* local ... *)
end

(* functor Search *)
(* Basic search engine: Version 1.3*)

(* Author: Carsten Schuermann *)

module type MTPSEARCH = sig
  module StateSyn : STATESYN

  exception Error of string

  val searchEx :
    int * IntSyn.exp list (*      * (IntSyn.Exp * IntSyn.Sub) *) * (int -> unit) ->
    unit
end

(* signature SEARCH *)
