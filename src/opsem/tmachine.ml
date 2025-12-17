TMachine  Unify UNIFY    Assign ASSIGN    Index INDEX    CPrint CPRINT    Names NAMES    Trace TRACE     ABSMACHINE  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
module module module module (* We write
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
let rec compose(g,  , null) g compose(g,  , decl (g',  , d)) decl (compose (g,  , g'),  , d)let rec shiftSub(null,  , s) s shiftSub(decl (g,  , d),  , s) dot1 (shiftSub (g,  , s))let rec subgoalNum(nil) 1 subgoalNum(app (u,  , s)) 1 + subgoalNum s(* currently unused *)
let rec goalToType(all (d,  , g),  , s) pi ((decSub (d,  , s),  , maybe),  , goalToType (g,  , dot1 s)) goalToType(impl (_,  , a,  , _,  , g),  , s) pi ((dec (nONE,  , eClo (a,  , s)),  , no),  , goalToType (g,  , dot1 s)) goalToType(atom (p),  , s) eClo (p,  , s)(* solve' ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated to

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
let rec solve'((atom (p),  , s),  , dp as dProg (g,  , dPool),  , sc) matchAtom ((p,  , s),  , dp,  , sc) solve'((impl (r,  , a,  , ha,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  inlet  in in solve' ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (fun m -> (signal (g,  , dischargeHyp (ha,  , d')); sc (lam (d',  , m))))) solve'((all (d,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  inlet  inlet  in in solve' ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , (fun m -> (signal (g,  , dischargeParm (ha,  , d')); sc (lam (d',  , m)))))(* rSolve' ((p,s'), (r,s), dp, (Hc, Ha), sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
       Hc is the clause which generated this residual goal
       Ha is the target family of p and r (which must be equal)
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
 rSolve(ps',  , (eq (q),  , s),  , dProg (g,  , dPool),  , hcHa,  , sc) (signal (g,  , unify (hcHa,  , eClo (q,  , s),  , eClo ps')); match unifiable' (g,  , (q,  , s),  , ps')(* effect: instantiate EVars *)
 with nONE -> (signal (g,  , resolved hcHa); sc nil; (* call success continuation *)
true)(* deep backtracking *)
 sOME (msg) -> (signal (g,  , failUnify (hcHa,  , msg)); false)) rSolve(ps',  , (assign (q,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , hcHa,  , sc) ((* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); *)
match assignable (g,  , ps',  , (q,  , s)) with sOME (cnstr) -> aSolve ((eqns,  , s),  , dp,  , hcHa,  , cnstr,  , (fun () -> sc nil)) nONE -> ((* T.signal (G, T.FailUnify (HcHa, "Assignment failed")); *)
false)) rSolve(ps',  , (and (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , hcHa,  , sc) let (* is this EVar redundant? -fp *)
let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , hcHa,  , (fun s -> (signal (g,  , subgoal (hcHa,  , fun () -> subgoalNum s)); solve' ((g,  , s),  , dp,  , (fun m -> sc (app (m,  , s))))))) rSolve(ps',  , (exists (dec (_,  , a),  , r),  , s),  , dp as dProg (g,  , dPool),  , hcHa,  , sc) let let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , hcHa,  , (fun s -> sc (app (x,  , s)))) rSolve(ps',  , (axists (aDec (_,  , d),  , r),  , s),  , dp as dProg (g,  , dPool),  , hcHa,  , sc) let let  in in rSolve (ps',  , (r,  , dot (exp (eClo (x,  , shift (~ d))),  , s)),  , dp,  , hcHa,  , sc)(* we don't increase the proof term here! *)
(* aSolve ((ag, s), dp, HcHa, sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated

     Effects: instantiation of EVars in ag[s], dp and sc () *)
 aSolve((trivial,  , s),  , dp as dProg (g,  , dPool),  , hcHa,  , cnstr,  , sc) if solveCnstr cnstr then (signal (g,  , resolved hcHa); sc (); true) else ((* T.signal (G, T.FailUnify (HcHa, "Dynamic residual equations failed")); *)
false) aSolve((unifyEq (g',  , e1,  , n,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , hcHa,  , cnstr,  , sc) let let  inlet  in in if unifiable (g'',  , (n,  , s'),  , (e1,  , s')) then aSolve ((eqns,  , s),  , dp,  , hcHa,  , cnstr,  , sc) else ((* T.signal (G, T.FailUnify (HcHa, "Static residual equations failed")); *)
false)(* matchatom ((p, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else res = False
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
 matchAtom(ps' as (root (ha,  , s),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  inlet  inlet  inexception (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
let rec matchSignil (signal (g,  , failGoal (tag,  , ha,  , eClo ps')); ()) matchSig(hc :: sgn') let let  in in (* trail to undo EVar instantiations *)
if trail (fun () -> rSolve (ps',  , (r,  , id),  , dp,  , (hc,  , ha),  , (fun s -> (signal (g,  , succeedGoal (tag,  , (hc,  , ha),  , eClo ps')); sc (root (hc,  , s)))))) then (* deep backtracking *)
(signal (g,  , retryGoal (tag,  , (hc,  , ha),  , eClo ps')); ()) else (* shallow backtracking *)
()matchSig sgn'(* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1. -- succeeds exactly once

           succeeds exactly once (#succeeds = 1)
        *)
let rec matchSigDetnil (signal (g,  , failGoal (tag,  , ha,  , eClo ps')); ()) matchSigDet(hc :: sgn') let let  in in (* trail to undo EVar instantiations *)
try  with (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
let rec matchDProg(null,  , _) if deterministic then matchSigDet (lookup (cidFromHead ha)) else matchSig (lookup (cidFromHead ha)) matchDProg(decl (dPool',  , dec (r,  , s,  , ha')),  , k) if eqHead (ha,  , ha') then (if deterministic then (* #succeeds = 1 *)
(try  with ) else (* #succeeds >= 1 -- allows backtracking *)
(if trail (fun () -> rSolve (ps',  , (r,  , comp (s,  , shift (k))),  , dp,  , (bVar (k),  , ha),  , (fun s -> (succeedGoal (tag,  , (bVar (k),  , ha),  , eClo ps'); sc (root (bVar (k),  , s)))))) then (* deep backtracking *)
(signal (g,  , retryGoal (tag,  , (bVar (k),  , ha),  , eClo ps')); ()) else (* shallow backtracking *)
(); matchDProg (dPool',  , k + 1))) else matchDProg (dPool',  , k + 1) matchDProg(decl (dPool',  , parameter),  , k) matchDProg (dPool',  , k + 1)let rec matchConstraint(cnstrSolve,  , try) let let  in in if succeeded then matchConstraint (cnstrSolve,  , try + 1) else () in match constStatus (cidFromHead ha) with (constraint (cs,  , cnstrSolve)) -> matchConstraint (cnstrSolve,  , 0) _ -> matchDProg (dPool,  , 1)let rec solve(gs,  , dp,  , sc) (init (); solve' (gs,  , dp,  , sc))(* local ... *)
end