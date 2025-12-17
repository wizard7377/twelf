AbsMachineSbt  Unify UNIFY    SubTree SUBTREE    Assign ASSIGN    Index INDEX    CPrint CPRINT    Print PRINT    Names NAMES     ABSMACHINESBT  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
module module let  in(* We write
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
let rec cidFromHead(const a) a cidFromHead(def a) alet rec eqHead(const a,  , const a') a = a' eqHead(def a,  , def a') a = a' eqHead_ false(* Wed Mar 13 10:27:00 2002 -bp  *)
(* should probably go to intsyn.fun *)
let rec compose'(null,  , g) g compose'(decl (g,  , d),  , g') decl (compose' (g,  , g'),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))let rec invShiftN(n,  , s) if n = 0 then comp (invShift,  , s) else comp (invShift,  , invShiftN (n - 1,  , s))let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , pi ((d,  , maybe),  , v))let rec printSub(shift n) print ("Shift " ^ toString n ^ "\n") printSub(dot (idx n,  , s)) (print ("Idx " ^ toString n ^ " . "); printSub s) printSub(dot (exp (eVar (_,  , _,  , _,  , _)),  , s)) (print ("Exp (EVar _ ). "); printSub s) printSub(dot (exp (aVar (_)),  , s)) (print ("Exp (AVar _ ). "); printSub s) printSub(dot (exp (eClo (aVar (_),  , _)),  , s)) (print ("Exp (AVar _ ). "); printSub s) printSub(dot (exp (eClo (_,  , _)),  , s)) (print ("Exp (EClo _ ). "); printSub s) printSub(dot (exp (_),  , s)) (print ("Exp (_ ). "); printSub s) printSub(dot (undef,  , s)) (print ("Undef . "); printSub s)(* ctxToEVarSub D = s*)
let rec ctxToEVarSub(gglobal,  , null,  , s) s ctxToEVarSub(gglobal,  , decl (g,  , dec (_,  , a)),  , s) let let  inlet  in in dot (exp (x),  , s') ctxToEVarSub(gglobal,  , decl (g,  , aDec (_,  , d)),  , s) let let  in in dot (exp (eClo (x,  , shift (~ d))),  , ctxToEVarSub (gglobal,  , g,  , s))(* solve' ((g, s), dp, sc) = res
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
let rec solve'((atom (p),  , s),  , dp as dProg (g,  , dpool),  , sc) matchAtom ((p,  , s),  , dp,  , sc) solve'((impl (r,  , a,  , ha,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  in in solve' ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , sc) solve'((all (d,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  in in solve' ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , sc)(* rSolve ((p,s'), (r,s), dp, sc) = res
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
 rSolve(ps',  , (eq (q),  , s),  , dProg (g,  , dPool),  , sc) (if unifiable (g,  , ps',  , (q,  , s))(* effect: instantiate EVars *)
 then sc nil(* call success continuation *)
 else ()) rSolve(ps',  , (assign (q,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , sc) (match assignable (g,  , ps',  , (q,  , s)) with sOME (cnstr) -> aSolve ((eqns,  , s),  , dp,  , cnstr,  , (fun () -> sc nil)) nONE -> ()) rSolve(ps',  , (and (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , sc) let (* is this EVar redundant? -fp *)
let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun skel1 -> solve' ((g,  , s),  , dp,  , (fun skel2 -> sc (skel1 @ skel2))))) rSolve(ps',  , (exists (dec (_,  , a),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , sc) rSolve(ps',  , (axists (aDec (_,  , d),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  in in rSolve (ps',  , (r,  , dot (exp (eClo (x',  , shift (~ d))),  , s)),  , dp,  , sc)(* we don't increase the proof term here! *)
(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
 aSolve((trivial,  , s),  , dp,  , cnstr,  , sc) (if solveCnstr cnstr then sc () else ()(* Fail *)
) aSolve((unifyEq (g',  , e1,  , n,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , cnstr,  , sc) let let  inlet  in in if unifiable (g'',  , (n,  , s'),  , (e1,  , s')) then aSolve ((eqns,  , s),  , dp,  , cnstr,  , sc) else ()(* Fail *)
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
 sSolve((true,  , s),  , dp,  , sc) sc nil sSolve((conjunct (g,  , a,  , sgoals),  , s),  , dp as dProg (g,  , dPool),  , sc) solve' ((g,  , s),  , dp,  , (fun skel1 -> sSolve ((sgoals,  , s),  , dp,  , (fun skel2 -> sc (skel1 @ skel2)))))(* match signature *)
 matchSig(ps' as (root (ha,  , s),  , s),  , dp as dProg (g,  , dPool),  , sc) let let rec mSignil () mSig((hc as const c) :: sgn') let let  in in (* trail to undo EVar instantiations *)
trail (fun () -> rSolve (ps',  , (r,  , id),  , dp,  , (fun s -> sc ((pc c) :: s))))mSig (sgn') in mSig (lookup (cidFromHead ha)) matchIndexSig(ps' as (root (ha,  , s),  , s),  , dp as dProg (g,  , dPool),  , sc) matchSig (cidFromHead ha,  , g,  , ps',  , (fun ((conjGoals,  , s),  , clauseName) -> sSolve ((conjGoals,  , s),  , dp,  , (fun s -> sc ((pc clauseName) :: s)))))(* matchatom ((p, s), dp, sc) => res
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
 matchAtom(ps' as (root (ha,  , s),  , s),  , dp as dProg (g,  , dPool),  , sc) let (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
let rec matchDProg(null,  , _) (! mSig) (ps',  , dp,  , sc) matchDProg(decl (dPool',  , dec (r,  , s,  , ha')),  , k) if eqHead (ha,  , ha') then (trail (* trail to undo EVar instantiations *)
 (fun () -> rSolve (ps',  , (r,  , comp (s,  , shift (k))),  , dp,  , (fun s -> sc ((dc k) :: s)))); matchDProg (dPool',  , k + 1)) else matchDProg (dPool',  , k + 1) matchDProg(decl (dPool',  , parameter),  , k) matchDProg (dPool',  , k + 1)let rec matchConstraint(solve,  , try) let let  in in if succeeded then matchConstraint (solve,  , try + 1) else () in match constStatus (cidFromHead ha) with (constraint (cs,  , solve)) -> matchConstraint (solve,  , 0) _ -> matchDProg (dPool,  , 1)let rec solveargs (match (! optimize) with no -> (mSig := matchSig; solve' args) linearHeads -> (mSig := matchSig; solve' args) indexing -> (mSig := matchIndexSig; solve' args))(* local ... *)
end