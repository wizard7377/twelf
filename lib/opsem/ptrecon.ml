open Basis ;; 
(* Abstract Machine guided by proof skeleton *)

(* Author: Brigitte Pientks *)

(* Modified: Jeff Polakow *)

(* Modified: Frank Pfenning *)

(* Proof term reconstruction by proof skeleton *)

module type PTRECON = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure CompSyn : Compsyn.COMPSYN !*)
  exception Error of string

  val solve :
    CompSyn.pskeleton
    * (CompSyn.goal * IntSyn.sub)
    * CompSyn.dProg
    * (CompSyn.pskeleton * IntSyn.exp -> unit) ->
    unit
end

(* signature PTRECON *)
(* Abstract Machine execution guided by proof skeleton *)

(* Author: Brigitte Pientka *)

(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga, Brigitte Pientka *)

(* Proof term reconstruction from proof skeleton *)

module PtRecon
    (Unify : Unify.UNIFY)
    (Assign : Assign.ASSIGN)
    (MemoTable : Subtree.Sw_subtree.MEMOTABLE)
    (Index : Index.INDEX)
    (CPrint : Cprint.CPRINT)
    (Names : Names.NAMES) : PTRECON = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure CompSyn = CompSyn' !*)

  (*! structure TableParam = TableParam !*)

  module I = IntSyn
  module C = CompSyn
  module MT = MemoTable

  exception Error of string

  let rec cidFromHead = function I.Const a -> a | I.Def a -> a

  let rec eqHead = function
    | I.Const a, I.Const a' -> a = a'
    | I.Def a, I.Def a' -> a = a'
    | _ -> false

  let rec compose' = function
    | IntSyn.Null, G -> G
    | IntSyn.Decl (G, D), G' -> IntSyn.Decl (compose' (G, G'), D)

  let rec shift = function
    | IntSyn.Null, s -> s
    | IntSyn.Decl (G, D), s -> I.dot1 (shift (G, s))
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

     Non-determinism within the rules is resolved by oracle
  *)

  (* solve' (o, (g, s), dp, sc) => ()
     Invariants:
       o = oracle
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)

  let rec solve' = function
    | O, (C.Atom p, s), dp, sc -> matchAtom (O, (p, s), dp, sc)
    | O, (C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc ->
        let D' = I.Dec (None, I.EClo (A, s)) in
        if !TableParam.strengthen then
          match MT.memberCtx ((G, I.EClo (A, s)), G) with
          | Some D ->
              let X = I.newEVar (G, I.EClo (A, s)) in
              (* need to reuse label for_sml this assumption .... *)
              solve'
                ( O,
                  (g, I.Dot (I.Exp X, s)),
                  C.DProg (G, dPool),
                  fun (O, M) -> sc (O, I.Lam (D', M)) )
          | None ->
              solve'
                ( O,
                  (g, I.dot1 s),
                  C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
                  fun (O, M) -> sc (O, I.Lam (D', M)) )
        else
          solve'
            ( O,
              (g, I.dot1 s),
              C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
              fun (O, M) -> sc (O, I.Lam (D', M)) )
        (*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*)
    | O, (C.All (D, g), s), C.DProg (G, dPool), sc ->
        (* val D' = I.decSub (D, s) *)
        let D' = Names.decLUName (G, I.decSub (D, s)) in
        solve'
          ( O,
            (g, I.dot1 s),
            C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
            fun (O, M) -> sc (O, I.Lam (D', M)) )

  and rSolve = function
    | O, ps', (C.Eq Q, s), C.DProg (G, dPool), sc ->
        if Unify.unifiable (G, (Q, s), ps') (* effect: instantiate EVars *) then
          sc (O, I.Nil) (* call success continuation *)
        else
          let _ =
            print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
            print (Print.expToString (G, I.EClo ps') ^ " unify ");
            print (Print.expToString (G, I.EClo (Q, s)) ^ "\n")
          in
          ()
    | O, ps', (C.Assign (Q, eqns), s), dp, sc -> (
        match Assign.assignable (G, ps', (Q, s)) with
        | Some cnstr ->
            if aSolve ((eqns, s), dp, cnstr) then sc (O, I.Nil)
            else print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
        | None -> print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n")
    | O, ps', (C.And (r, A, g), s), dp, sc ->
        (* is this EVar redundant? -fp *)
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( O,
            ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            fun (O, S) ->
              solve' (O, (g, s), dp, fun (O, M) -> sc (O, I.App (M, S))) )
    | O, ps', (C.Exists (I.Dec (_, A), r), s), dp, sc ->
        let X = I.newEVar (G, I.EClo (A, s)) in
        rSolve
          ( O,
            ps',
            (r, I.Dot (I.Exp X, s)),
            dp,
            fun (O, S) -> sc (O, I.App (X, S)) )
    | O, ps', (C.Axists (I.ADec (Some X, d), r), s), dp, sc ->
        let X' = I.newAVar () in
        rSolve (O, ps', (r, I.Dot (I.Exp (I.EClo (X', I.Shift ~-d)), s)), dp, sc)
  (* we don't increase the proof term here! *)

  and aSolve = function
    | (C.Trivial, s), dp, cnstr -> Assign.solveCnstr cnstr
    | (C.UnifyEq (G', e1, N, eqns), s), dp, cnstr ->
        let G'' = compose' (G', G) in
        let s' = shift (G', s) in
        Assign.unifiable (G'', (N, s'), (e1, s'))
        && aSolve ((eqns, s), dp, cnstr)

  and matchAtom (Ho :: O, ps', dp, sc) =
    (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for_sml solving atomic goal ps', starting
           with c1.
        *)
    (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for_sml solving atomic goal ps', starting
           with the most recent one.
        *)
    let rec matchSig = function
      | [], k -> raise (Error " \noracle #Pc does not exist \n")
      | Hc :: sgn', k ->
          if c = k then
            let (C.SClause r) = C.sProgLookup (cidFromHead Hc) in
            rSolve (O, ps', (r, I.id), dp, fun (O, S) -> sc (O, I.Root (Hc, S)))
          else matchSig (sgn', k)
      | Hc :: sgn', k ->
          if d = k then
            let (C.SClause r) = C.sProgLookup (cidFromHead Hc) in
            rSolve (O, ps', (r, I.id), dp, fun (O, S) -> sc (O, I.Root (Hc, S)))
          else matchSig (sgn', k)
    in
    let rec matchDProg = function
      | I.Null, i, k ->
          raise
            (Error
               "\n\
               \ selected dynamic clause number does not exist in current \
                dynamic clause pool!\n")
      | I.Decl (dPool', C.Dec (r, s, Ha')), 1, k ->
          if eqHead (Ha, Ha') then
            rSolve
              ( O,
                ps',
                (r, I.comp (s, I.Shift k)),
                dp,
                fun (O, S) -> sc (O, I.Root (I.BVar k, S)) )
          else (* shouldn't happen *)
            raise
              (Error "\n selected dynamic clause does not match current goal!\n")
      | I.Decl (dPool', dc), i, k -> matchDProg (dPool', i - 1, k)
    in
    match Ho with
    | C.Pc i -> matchSig (Index.lookup (cidFromHead Ha), i)
    | C.Dc i -> matchDProg (dPool, i, i)
    | C.Csolver U -> sc (O, U)

  let rec solve (O, (g, s), dp, sc) =
    try solve' (O, (g, s), dp, sc) with Error msg -> print msg
  (* local ... *)
end

(* functor PtRecon *)
