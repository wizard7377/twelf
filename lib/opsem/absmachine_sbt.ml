(* Abstract Machine using substitution trees *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) AbsMachineSbt ((*! structure IntSyn' : INTSYN !*)
                       (*! structure CompSyn' : COMPSYN !*)
                       (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                       structure Unify : UNIFY
                       (*! sharing Unify.IntSyn = IntSyn' !*)
                       structure SubTree : SUBTREE
                       (*! sharing SubTree.IntSyn = IntSyn' !*)
                       (*! sharing SubTree.CompSyn = CompSyn' !*)
                       structure Assign : ASSIGN
                       (*! sharing Assign.IntSyn = IntSyn' !*)

                       structure Index : INDEX
                       (*! sharing Index.IntSyn = IntSyn' !*)
                       (* CPrint currently unused *)
                       structure CPrint : CPRINT
                       (*! sharing CPrint.IntSyn = IntSyn' !*)
                       (*! sharing CPrint.CompSyn = CompSyn' !*)

                       structure Print : PRINT
                       (*! sharing Print.IntSyn = IntSyn' !*)

                       structure Names : NAMES
                       (*! sharing Names.IntSyn = IntSyn' !*)
                       (*! structure CSManager : CS_MANAGER !*)
                       (*! sharing CSManager.IntSyn = IntSyn'!*))
  : ABSMACHINESBT =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)

  local
    structure I = IntSyn
    structure C = CompSyn

    (* GEN BEGIN TAG OUTSIDE LET *) val mSig : ((IntSyn.exp * IntSyn.sub) * CompSyn.d_prog * (CompSyn.flatterm list -> unit) -> unit) ref = ref ((* GEN BEGIN FUNCTION EXPRESSION *) fn (ps, dp, sc) => () (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

  (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)

  fun (* GEN BEGIN FUN FIRST *) cidFromHead (I.Const a) = a (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) cidFromHead (I.Def a) = a (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) eqHead (I.Const a, I.Const a') = a = a' (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) eqHead (I.Def a, I.Def a') = a = a' (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) eqHead _ = false (* GEN END FUN BRANCH *)

  (* Wed Mar 13 10:27:00 2002 -bp  *)
  (* should probably go to intsyn.fun *)
  fun (* GEN BEGIN FUN FIRST *) compose'(IntSyn.Null, G) = G (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) shift (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s)) (* GEN END FUN BRANCH *)

 fun invShiftN (n, s) =
   if n = 0 then I.comp(I.invShift, s)
   else I.comp(I.invShift, invShiftN(n-1, s))

 fun (* GEN BEGIN FUN FIRST *) raiseType (I.Null, V) = V (* GEN END FUN FIRST *)
   | (* GEN BEGIN FUN BRANCH *) raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V)) (* GEN END FUN BRANCH *)


  fun (* GEN BEGIN FUN FIRST *) printSub (IntSyn.Shift n) = print ("Shift " ^ Int.toString n ^ "\n") (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot(IntSyn.Idx n, s)) = (print ("Idx " ^ Int.toString n ^ " . "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.EVar (_, _, _, _)), s)) = (print ("Exp (EVar _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.AVar (_)), s)) = (print ("Exp (AVar _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.EClo (IntSyn.AVar (_), _)), s)) = (print ("Exp (AVar _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(IntSyn.EClo (_, _)), s)) = (print ("Exp (EClo _ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Exp(_), s)) = (print ("Exp (_ ). "); printSub s) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) printSub (IntSyn.Dot (IntSyn.Undef, s)) = (print ("Undef . "); printSub s) (* GEN END FUN BRANCH *)

  (* ctxToEVarSub D = s*)

    fun (* GEN BEGIN FUN FIRST *) ctxToEVarSub (Gglobal, I.Null, s) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) ctxToEVarSub (Gglobal, I.Decl(G,I.Dec(_,A)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = ctxToEVarSub (Gglobal, G, s) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (Gglobal, I.EClo(A,s')) (* GEN END TAG OUTSIDE LET *)
      in
        I.Dot(I.Exp(X),s')
      end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) ctxToEVarSub (Gglobal, I.Decl(G,I.ADec(_,d)), s) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), ctxToEVarSub (Gglobal, G, s))
      end (* GEN END FUN BRANCH *)


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
  fun (* GEN BEGIN FUN FIRST *) solve' ((C.Atom(p), s), dp as C.DProg (G, dpool), sc)  =
       matchAtom ((p,s), dp, sc) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) solve' ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.Dec(NONE, I.EClo(A,s)) (* GEN END TAG OUTSIDE LET *)
      in
        solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))), sc)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) solve' ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, I.decSub (D, s)) (* GEN END TAG OUTSIDE LET *)
      in
        solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)), sc)
      end (* GEN END FUN BRANCH *)

  (* rSolve ((p,s'), (r,s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and (* GEN BEGIN FUN FIRST *) rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc)  =
      (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
         then sc nil                       (* call success continuation *)
       else ()) (* GEN END FUN FIRST *)                            (* fail *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
        (case Assign.assignable (G, ps', (Q, s))
           of SOME(cnstr) => aSolve ((eqns, s), dp, cnstr,
                                     ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => sc nil (* GEN END FUNCTION EXPRESSION *)))
            | NONE => ()) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
        (* is this EVar redundant? -fp *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo(A, s)) (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn skel1 => solve' ((g, s), dp,
                                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn skel2 => sc (skel1 @ skel2) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)))
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo (A,s)) (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, sc)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Axists(I.ADec(_, d), r), s), dp as C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X' = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
        (* we don't increase the proof term here! *)
      end (* GEN END FUN BRANCH *)


  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and (* GEN BEGIN FUN FIRST *) aSolve ((C.Trivial, s), dp, cnstr, sc) =
      (if Assign.solveCnstr cnstr
         then
           sc ()
       else () (* Fail *)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val G'' = compose' (G', G) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = shift (G', s) (* GEN END TAG OUTSIDE LET *)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s'))
          then  aSolve ((eqns, s), dp, cnstr, sc)
        else ()   (* Fail *)
     end (* GEN END FUN BRANCH *)

 (* solve subgoals of static program clauses *)
(* sSolve ((sg, s) , dp , sc =
 if  dp = (G, dPool) where G ~ dPool
     G |- s : G'
     sg = g1 and g2 ...and gk
     for every subgoal gi, G' |- gi
                           G  | gi[s]
   then
      sc () is evaluated
   else Fail

   Effects: instantiation of EVars in gi[s], dp, sc
*)
  and (* GEN BEGIN FUN FIRST *) sSolve ((C.True, s), dp, sc) = sc nil (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) sSolve ((C.Conjunct (g, A, Sgoals), s), dp as C.DProg(G, dPool), sc) =
    solve' ((g,s), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn skel1 => sSolve ((Sgoals, s), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn skel2 => sc (skel1 @ skel2) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUN BRANCH *)

   (* match signature *)
  and matchSig (ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) =
      let
        fun (* GEN BEGIN FUN FIRST *) mSig nil = () (* GEN END FUN FIRST *)       (* return on failure *)
          | (* GEN BEGIN FUN BRANCH *) mSig ((Hc as I.Const c)::sgn') =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val C.SClause(r) = C.sProgLookup (cidFromHead Hc) (* GEN END TAG OUTSIDE LET *)
          in
            (* trail to undo EVar instantiations *)
            CSManager.trail
            ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
             rSolve (ps', (r, I.id), dp,
                     ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc ((C.Pc c) :: S) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *));
             mSig (sgn')
          end (* GEN END FUN BRANCH *)
      in
        mSig(Index.lookup (cidFromHead Ha))
      end

   and matchIndexSig (ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) =
         SubTree.matchSig (cidFromHead Ha, G, ps',
                           ((* GEN BEGIN FUNCTION EXPRESSION *) fn ((ConjGoals, s), clauseName) =>
                            sSolve ((ConjGoals, s), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc ((C.Pc clauseName) :: S) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)))

  (* matchatom ((p, s), dp, sc) => res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G, dPool), sc) =
      let
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
        fun (* GEN BEGIN FUN FIRST *) matchDProg (I.Null, _) =
            (* dynamic program exhausted, try signature
               there is a choice depending on how we compiled signature
             *)
          (!mSig) (ps', dp, sc) (* GEN END FUN FIRST *)
  
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Dec(r, s, Ha')), k) =
            if eqHead (Ha, Ha')
              then (CSManager.trail (* trail to undo EVar instantiations *)
                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                      ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc ((C.Dc k) :: S) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *));
                    matchDProg (dPool', k+1))
            else matchDProg (dPool', k+1) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Parameter), k) =
              matchDProg (dPool', k+1) (* GEN END FUN BRANCH *)
  
         fun matchConstraint (solve, try) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val succeeded =
                  CSManager.trail
                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                       case (solve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc [C.Csolver U]; true)
                          | NONE => false (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
              in
                if succeeded
                then  matchConstraint (solve, try+1)
                else ()
              end
      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)
      end

  in
    fun solve args  =
      (case (!CompSyn.optimize) of
         CompSyn.No => (mSig := matchSig ; solve' args)
       | CompSyn.LinearHeads => (mSig := matchSig; solve' args)
       | CompSyn.Indexing => (mSig := matchIndexSig; solve' args))
  end (* local ... *)

end (* GEN END FUNCTOR DECL *); (* functor AbsMachineSbt *)


