(* Search (based on abstract machine ) *)

(* Author: Carsten Schuermann *)

module OLDSearch
    (MetaGlobal : METAGLOBAL)
    (MetaSyn' : METASYN)
    (Whnf : WHNF)
    (Unify : UNIFY)
    (Index : INDEX)
    (Compile : COMPILE)
    (CPrint : CPRINT)
    (Print : PRINT)
    (Names : NAMES) : OLDSEARCH = struct
  (*! structure IntSyn = IntSyn' !*)

  module MetaSyn = MetaSyn'
  (*! structure CompSyn = CompSyn' !*)

  exception Error of string

  module I = IntSyn
  module M = MetaSyn
  module C = CompSyn

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
    | (C.Atom p, s), dp, sc, acck -> matchAtom ((p, s), dp, sc, acck)
    | (C.Impl (r, A, H, g), s), C.DProg (G, dPool), sc, acck ->
        let D' = I.Dec (None, I.EClo (A, s)) in
        solve
          ( (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, H))),
            (fun (M, acck') -> sc (I.Lam (D', M), acck')),
            acck )
    | (C.All (D, g), s), C.DProg (G, dPool), sc, acck ->
        let D' = I.decSub (D, s) in
        solve
          ( (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
            (fun (M, acck') -> sc (I.Lam (D', M), acck')),
            acck )

  and rSolve = function
    | ps', (C.Eq Q, s), C.DProg (G, dPool), sc, acck ->
        if Unify.unifiable (G, ps', (Q, s)) then sc (I.Nil, acck) else acc
    | ps', (C.And (r, A, g), s), dp, sc, acck ->
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            (fun (S, acck') ->
              solve
                ( (g, s),
                  dp,
                  (fun (M, acck'') ->
                    try
                      Unify.unify (G, (X, I.id), (M, I.id));
                      (* why doesn't it always succeed?
                                                                --cs *)
                      sc (I.App (M, S), acck'')
                    with Unify.Unify _ -> []),
                  acck' )),
            acck )
    | ps', (C.Exists (I.Dec (_, A), r), s), dp, sc, acck ->
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            (fun (S, acck') -> sc (I.App (X, S), acck')),
            acck )

  and aSolve ((C.Trivial, s), dp, sc, acc) = sc ()

  and matchAtom (ps', dp, sc, (acc, k)) =
    let rec matchSig acc' =
      let rec matchSig' = function
        | [], acc'' -> acc''
        | Hc :: sgn', acc'' ->
            let (C.SClause r) = C.sProgLookup (cidFromHead Hc) in
            let acc''' =
              CSManager.trail (fun () ->
                  rSolve
                    ( ps',
                      (r, I.id),
                      dp,
                      (fun (S, acck') -> sc (I.Root (Hc, S), acck')),
                      (acc'', k - 1) ))
            in
            matchSig' (sgn', acc''')
      in
      matchSig' (Index.lookup (cidFromHead Ha), acc')
    in
    let rec matchDProg = function
      | I.Null, _, acc' -> matchSig acc'
      | I.Decl (dPool', C.Dec (r, s, Ha')), n, acc' ->
          if eqHead (Ha, Ha') then
            let acc'' =
              CSManager.trail (fun () ->
                  rSolve
                    ( ps',
                      (r, I.comp (s, I.Shift n)),
                      dp,
                      (fun (S, acck') -> sc (I.Root (I.BVar n, S), acck')),
                      (acc', k - 1) ))
            in
            matchDProg (dPool', n + 1, acc'')
          else matchDProg (dPool', n + 1, acc')
      | I.Decl (dPool', C.Parameter), n, acc' -> matchDProg (dPool', n + 1, acc')
    in
    if k < 0 then acc else matchDProg (dPool, 1, acc)
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
       If   GE is a list of Evars
       and  G |- s : G'   G' |- V : L
       then acc' is a list of EVars (G', X') s.t.
         (0) it extends acc'
         (1) (G', X') occurs in V[s]
         (2) (G', X') is not an index Variable to any (G, X) in acc'.
    *)

  (* Efficiency: repeated whnf for_sml every subterm in Vs!!! *)

  let rec selectEVar = function
    | [], _, acc -> acc
    | X :: GE, Vs, acc ->
        if occursInExp (r, Vs) && nonIndex (r, acc) then
          selectEVar (GE, Vs, X :: acc)
        else selectEVar (GE, Vs, acc)
  (* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)

  (* contexts of EVars are recompiled for_sml each search depth *)

  let rec searchEx' = function
    | max, ([], sc) -> [ sc () ]
    | max, (I.EVar (r, G, V, _) :: GE, sc) ->
        solve
          ( (Compile.compileGoal (G, V), I.id),
            Compile.compileCtx false G,
            (fun (U', (acc', _)) ->
              Unify.instantiateEVar (r, U', []);
              searchEx' max (GE, sc)),
            ([], max) )
  (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MetaGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MetaGlobal.maxLevel
    *)

  let rec deepen f P =
    let rec deepen' (level, acc) =
      if level > !MetaGlobal.maxFill then acc
      else (
        if !Global.chatter > 5 then print "#" else ();
        deepen' (level + 1, f level P))
    in
    deepen' (1, [])
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

  let rec searchEx (G, GE, Vs, sc) =
    if !Global.chatter > 5 then print "[Search: " else ();
    deepen searchEx'
      ( selectEVar (GE, Vs, []),
        fun Params ->
          if !Global.chatter > 5 then print "OK]\n" else ();
          sc Params );
    if !Global.chatter > 5 then print "FAIL]\n" else ();
    raise (Error "No object found")
  (* searchAll' (GE, acc, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
         after trying all combinations of instantiations of EVars in GE
    *)

  (* Shared contexts of EVars in GE may recompiled many times *)

  let rec searchAll' = function
    | [], acc, sc -> sc acc
    | I.EVar (r, G, V, _) :: GE, acc, sc ->
        solve
          ( (Compile.compileGoal (G, V), I.id),
            Compile.compileCtx false G,
            (fun (U', (acc', _)) ->
              Unify.instantiateEVar (r, U', []);
              searchAll' (GE, acc', sc)),
            (acc, !MetaGlobal.maxFill) )
  (* searchAll (G, GE, (V, s), sc) = acc'

       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list of results from executing the success continuation
    *)

  let rec searchAll (G, GE, Vs, sc) =
    searchAll' (selectEVar (GE, Vs, []), [], sc)

  let searchEx = searchEx
  let searchAll = searchAll
  (* local ... *)
end

(* functor Search *)
(* Basic search engine *)

(* Author: Carsten Schuermann *)

module type OLDSEARCH = sig
  module MetaSyn : METASYN

  exception Error of string

  val searchEx :
    IntSyn.dctx * IntSyn.exp list * (IntSyn.exp * IntSyn.sub) * (unit -> unit) ->
    MetaSyn.state list

  val searchAll :
    IntSyn.dctx
    * IntSyn.exp list
    * (IntSyn.exp * IntSyn.sub)
    * (MetaSyn.state list -> MetaSyn.state list) ->
    MetaSyn.state list
end

(* signature SEARCH *)
