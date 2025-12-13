(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) AbsMachine ((*! structure IntSyn' : INTSYN !*)
                    (*! structure CompSyn' : COMPSYN !*)
                    (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                    structure Unify : UNIFY
                    (*! sharing Unify.IntSyn = IntSyn' !*)

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
                    (*! sharing CSManager.IntSyn = IntSyn' !*)
                        )
  : ABSMACHINE =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)

  local
    structure I = IntSyn
    structure C = CompSyn

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
  fun (* GEN BEGIN FUN FIRST *) compose (G, IntSyn.Null) = G (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compose (G, IntSyn.Decl(G', D)) = IntSyn.Decl(compose(G, G'), D) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) shiftSub (IntSyn.Null, s) = s (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) shiftSub (IntSyn.Decl(G, D), s) = I.dot1 (shiftSub (G, s)) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) raiseType (I.Null, V) = V (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V)) (* GEN END FUN BRANCH *)

  (* solve ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun (* GEN BEGIN FUN FIRST *) solve ((C.Atom(p), s), dp as C.DProg (G, dPool), sc) =
      matchAtom ((p,s), dp, sc) (* GEN END FUN FIRST *)

    | (* GEN BEGIN FUN BRANCH *) solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = I.Dec(NONE, I.EClo(A,s)) (* GEN END TAG OUTSIDE LET *)
      in
        solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn M => sc (I.Lam (D', M)) (* GEN END FUNCTION EXPRESSION *)))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val D' = Names.decLUName (G, I.decSub (D, s)) (* GEN END TAG OUTSIDE LET *)
    (*      val D' = I.decSub (D, s) *)
      in
        solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)),
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn M => sc (I.Lam (D', M)) (* GEN END FUNCTION EXPRESSION *)))
      end (* GEN END FUN BRANCH *)

  (* rSolve ((p,s'), (r,s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and (* GEN BEGIN FUN FIRST *) rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc) =
       if Unify.unifiable (G, (Q, s), ps') (* effect: instantiate EVars *)
         then sc I.Nil                     (* call success continuation *)
       else () (* GEN END FUN FIRST *)                             (* fail *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
        (case Assign.assignable (G, ps', (Q, s))
           of SOME(cnstr) =>
                aSolve((eqns, s), dp, cnstr, ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => sc I.Nil (* GEN END FUNCTION EXPRESSION *)))
            | NONE => ()) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
        (* is this EVar redundant? -fp *)
        (* same effect as s^-1 *)
        (* GEN BEGIN TAG OUTSIDE LET *) val X = I.newEVar (G, I.EClo(A, s)) (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
                ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => solve ((g, s), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn M => sc (I.App (M, S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)))
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X  = I.newEVar (G, I.EClo (A,s)) (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.App(X,S)) (* GEN END FUNCTION EXPRESSION *)))
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) rSolve (ps', (C.Axists(I.ADec(_, d), r), s), dp as C.DProg (G, dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val X' = I.newAVar () (* GEN END TAG OUTSIDE LET *)
      in
        rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
        (* we don't increase the proof term here! *)
      end (* GEN END FUN BRANCH *)

  (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and (* GEN BEGIN FUN FIRST *) aSolve ((C.Trivial, s), dp, cnstr, sc) =
      if Assign.solveCnstr cnstr then
        sc ()
      else () (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val G'' = compose (G, G') (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val s' = shiftSub (G', s) (* GEN END TAG OUTSIDE LET *)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s'))
        then
           aSolve ((eqns, s), dp, cnstr, sc)
        else ()
     end (* GEN END FUN BRANCH *)

  (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val deterministic = C.detTableCheck (cidFromHead Ha) (* GEN END TAG OUTSIDE LET *)
        exception SucceedOnce of I.spine
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
  
           #succeeds >= 1 (succeeds at least once)
        *)
        fun (* GEN BEGIN FUN FIRST *) matchSig nil = () (* GEN END FUN FIRST *)   (* return unit on failure *)
          | (* GEN BEGIN FUN BRANCH *) matchSig (Hc::sgn') =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val C.SClause(r) = C.sProgLookup (cidFromHead Hc) (* GEN END TAG OUTSIDE LET *)
            in
              (* trail to undo EVar instantiations *)
              CSManager.trail
              ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
               rSolve (ps', (r, I.id), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.Root(Hc, S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *));
              matchSig sgn'
            end (* GEN END FUN BRANCH *)
  
        (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
  
           succeeds exactly once (#succeeds = 1)
        *)
        fun (* GEN BEGIN FUN FIRST *) matchSigDet nil = () (* GEN END FUN FIRST *)        (* return unit on failure *)
          | (* GEN BEGIN FUN BRANCH *) matchSigDet (Hc::sgn') =
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val C.SClause(r) = C.sProgLookup (cidFromHead Hc) (* GEN END TAG OUTSIDE LET *)
            in
              (* trail to undo EVar instantiations *)
              (CSManager.trail
               ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => (rSolve (ps', (r, I.id), dp, ((* GEN BEGIN FUNCTION EXPRESSION *) fn S =>  raise SucceedOnce S (* GEN END FUNCTION EXPRESSION *)))) (* GEN END FUNCTION EXPRESSION *));
               matchSigDet sgn')
              handle SucceedOnce S =>  sc (I.Root(Hc, S))
            end (* GEN END FUN BRANCH *)
  
        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
        fun (* GEN BEGIN FUN FIRST *) matchDProg (I.Null, _) =
            (* dynamic program exhausted, try signature *)
          if deterministic
            then matchSigDet (Index.lookup (cidFromHead Ha))
          else matchSig (Index.lookup (cidFromHead Ha)) (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Dec(r, s, Ha')), k) =
            if eqHead (Ha, Ha')
            then
              if deterministic
                then (* #succeeds = 1 *)
                  ((CSManager.trail (* trail to undo EVar instantiations *)
                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                     ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => (raise SucceedOnce S) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *));
                    matchDProg (dPool', k+1))
                   handle SucceedOnce S => sc (I.Root(I.BVar(k), S)))
            
              else (* #succeeds >= 1 -- allows backtracking *)
                (CSManager.trail (* trail to undo EVar instantiations *)
                 ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                   ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => sc (I.Root(I.BVar(k), S)) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *));
                 matchDProg (dPool', k+1))
            else matchDProg (dPool', k+1) (* GEN END FUN BRANCH *)
          | (* GEN BEGIN FUN BRANCH *) matchDProg (I.Decl (dPool', C.Parameter), k) =
              matchDProg (dPool', k+1) (* GEN END FUN BRANCH *)
        fun matchConstraint (cnstrSolve, try) =
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val succeeded =
                  CSManager.trail
                    ((* GEN BEGIN FUNCTION EXPRESSION *) fn () =>
                       case (cnstrSolve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc U; true)
                          | NONE => false (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
              in
                if succeeded
                then matchConstraint (cnstrSolve, try+1)
                else ()
              end
      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, cnstrSolve)) => matchConstraint (cnstrSolve, 0)
           | _ => matchDProg (dPool, 1)
      end
  in
   (* GEN BEGIN TAG OUTSIDE LET *) val solve = solve (* GEN END TAG OUTSIDE LET *)
  end (* local ... *)

end (* GEN END FUNCTOR DECL *); (* functor AbsMachine *)
