(* Abstract Machine for_sml Tracing *)


(* Author: Frank Pfenning *)


(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)


module TMachine (Unify : UNIFY) (Assign : ASSIGN) (Index : INDEX) (CPrint : CPRINT) (Names : NAMES) (Trace : TRACE) : ABSMACHINE = struct (*! structure IntSyn = IntSyn' !*)

(*! structure CompSyn = CompSyn' !*)

module I = IntSyn
module C = CompSyn
module T = Trace
module N = Names
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

let rec cidFromHead = function (I.Const a) -> a | (I.Def a) -> a
let rec eqHead = function (I.Const a, I.Const a') -> a = a' | (I.Def a, I.Def a') -> a = a' | _ -> false
(* Wed Mar 13 10:27:00 2002 -bp  *)

(* should probably go to intsyn.fun *)

let rec compose = function (G, IntSyn.Null) -> G | (G, IntSyn.Decl (G', D)) -> IntSyn.Decl (compose (G, G'), D)
let rec shiftSub = function (IntSyn.Null, s) -> s | (IntSyn.Decl (G, D), s) -> I.dot1 (shiftSub (G, s))
let rec subgoalNum = function (I.Nil) -> 1 | (I.App (U, S)) -> 1 + subgoalNum S
(* currently unused *)

let rec goalToType = function (C.All (D, g), s) -> I.Pi ((I.decSub (D, s), I.Maybe), goalToType (g, I.dot1 s)) | (C.Impl (_, A, _, g), s) -> I.Pi ((I.Dec (None, I.EClo (A, s)), I.No), goalToType (g, I.dot1 s)) | (C.Atom (p), s) -> I.EClo (p, s)
(* solve' ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated to

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)

let rec solve' = function ((C.Atom (p), s), dp, sc) -> matchAtom ((p, s), dp, sc) | ((C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc) -> ( let D' = N.decUName (G, I.Dec (None, I.EClo (A, s))) in let _ = T.signal (G, T.IntroHyp (Ha, D')) in  solve' ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))), (fun M -> (T.signal (G, T.DischargeHyp (Ha, D')); sc (I.Lam (D', M))))) ) | ((C.All (D, g), s), C.DProg (G, dPool), sc) -> ( let D' = N.decUName (G, I.decSub (D, s)) in let Ha = I.targetHead V in let _ = T.signal (G, T.IntroParm (Ha, D')) in  solve' ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)), (fun M -> (T.signal (G, T.DischargeParm (Ha, D')); sc (I.Lam (D', M))))) )
and rSolve = function (ps', (C.Eq (Q), s), C.DProg (G, dPool), HcHa, sc) -> (T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); match Unify.unifiable' (G, (Q, s), ps')(* effect: instantiate EVars *)
 with None -> (T.signal (G, T.Resolved HcHa); sc I.Nil; (* call success continuation *)
true)(* deep backtracking *)
 | Some (msg) -> (T.signal (G, T.FailUnify (HcHa, msg)); false)) | (ps', (C.Assign (Q, eqns), s), dp, HcHa, sc) -> ((* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); *)
match Assign.assignable (G, ps', (Q, s)) with Some (cnstr) -> aSolve ((eqns, s), dp, HcHa, cnstr, (fun () -> sc I.Nil)) | None -> ((* T.signal (G, T.FailUnify (HcHa, "Assignment failed")); *)
false)) | (ps', (C.And (r, A, g), s), dp, HcHa, sc) -> ( (* is this EVar redundant? -fp *)
let X = I.newEVar (G, I.EClo (A, s)) in  rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp, HcHa, (fun S -> (T.signal (G, T.Subgoal (HcHa, fun () -> subgoalNum S)); solve' ((g, s), dp, (fun M -> sc (I.App (M, S))))))) ) | (ps', (C.Exists (I.Dec (_, A), r), s), dp, HcHa, sc) -> ( let X = I.newEVar (G, I.EClo (A, s)) in  rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp, HcHa, (fun S -> sc (I.App (X, S)))) ) | (ps', (C.Axists (I.ADec (_, d), r), s), dp, HcHa, sc) -> ( let X = I.newAVar () in  rSolve (ps', (r, I.Dot (I.Exp (I.EClo (X, I.Shift (~ d))), s)), dp, HcHa, sc)(* we don't increase the proof term here! *)
 )
and aSolve = function ((C.Trivial, s), dp, HcHa, cnstr, sc) -> if Assign.solveCnstr cnstr then (T.signal (G, T.Resolved HcHa); sc (); true) else ((* T.signal (G, T.FailUnify (HcHa, "Dynamic residual equations failed")); *)
false) | ((C.UnifyEq (G', e1, N, eqns), s), dp, HcHa, cnstr, sc) -> ( let G'' = compose (G, G') in let s' = shiftSub (G', s) in  if Assign.unifiable (G'', (N, s'), (e1, s')) then aSolve ((eqns, s), dp, HcHa, cnstr, sc) else ((* T.signal (G, T.FailUnify (HcHa, "Static residual equations failed")); *)
false) )
and matchAtom (ps', dp, sc)  = ( (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for_sml solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
(* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for_sml solving atomic goal ps', starting
           with c1. -- succeeds exactly once

           succeeds exactly once (#succeeds = 1)
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for_sml solving atomic goal ps', starting
           with the most recent one.
        *)
let tag = T.tagGoal () in let _ = T.signal (G, T.SolveGoal (tag, Ha, I.EClo ps')) in let deterministic = C.detTableCheck (cidFromHead Ha) in exception SucceedOnce of I.spine in let rec matchSig = function [] -> (T.signal (G, T.FailGoal (tag, Ha, I.EClo ps')); ()) | (Hc :: sgn') -> ( let C.SClause (r) = C.sProgLookup (cidFromHead Hc) in  (* trail to undo EVar instantiations *)
if CSManager.trail (fun () -> rSolve (ps', (r, I.id), dp, (Hc, Ha), (fun S -> (T.signal (G, T.SucceedGoal (tag, (Hc, Ha), I.EClo ps')); sc (I.Root (Hc, S)))))) then (* deep backtracking *)
(T.signal (G, T.RetryGoal (tag, (Hc, Ha), I.EClo ps')); ()) else (* shallow backtracking *)
(); matchSig sgn' ) in let rec matchSigDet = function [] -> (T.signal (G, T.FailGoal (tag, Ha, I.EClo ps')); ()) | (Hc :: sgn') -> ( let C.SClause (r) = C.sProgLookup (cidFromHead Hc) in  (* trail to undo EVar instantiations *)
try (if CSManager.trail (fun () -> rSolve (ps', (r, I.id), dp, (Hc, Ha), (fun S -> (T.signal (G, T.SucceedGoal (tag, (Hc, Ha), I.EClo ps')); raise (SucceedOnce S))))) then (* deep backtracking *)
(T.signal (G, T.RetryGoal (tag, (Hc, Ha), I.EClo ps')); ()) else (* shallow backtracking *)
(); matchSigDet sgn') with SucceedOnce S -> (T.signal (G, T.CommitGoal (tag, (Hc, Ha), I.EClo ps')); sc (I.Root (Hc, S))) ) in let rec matchDProg = function (I.Null, _) -> if deterministic then matchSigDet (Index.lookup (cidFromHead Ha)) else matchSig (Index.lookup (cidFromHead Ha)) | (I.Decl (dPool', C.Dec (r, s, Ha')), k) -> if eqHead (Ha, Ha') then (if deterministic then (* #succeeds = 1 *)
(try (if (CSManager.trail (* trail to undo EVar instantiations *)
 (fun () -> rSolve (ps', (r, I.comp (s, I.Shift (k))), dp, (I.BVar (k), Ha), (fun S -> (T.signal (G, T.SucceedGoal (tag, (I.BVar (k), Ha), I.EClo ps')); raise (SucceedOnce S)))))) then (* deep backtracking *)
(T.signal (G, T.RetryGoal (tag, (I.BVar (k), Ha), I.EClo ps')); ()) else (* shallow backtracking *)
(); matchDProg (dPool', k + 1)) with SucceedOnce S -> (T.signal (G, T.CommitGoal (tag, (I.BVar (k), Ha), I.EClo ps')); sc (I.Root (I.BVar (k), S)))) else (* #succeeds >= 1 -- allows backtracking *)
(if CSManager.trail (fun () -> rSolve (ps', (r, I.comp (s, I.Shift (k))), dp, (I.BVar (k), Ha), (fun S -> (T.SucceedGoal (tag, (I.BVar (k), Ha), I.EClo ps'); sc (I.Root (I.BVar (k), S)))))) then (* deep backtracking *)
(T.signal (G, T.RetryGoal (tag, (I.BVar (k), Ha), I.EClo ps')); ()) else (* shallow backtracking *)
(); matchDProg (dPool', k + 1))) else matchDProg (dPool', k + 1) | (I.Decl (dPool', C.Parameter), k) -> matchDProg (dPool', k + 1) in let rec matchConstraint (cnstrSolve, try_)  = ( let succeeded = CSManager.trail (fun () -> match (cnstrSolve (G, I.SClo (S, s), try_)) with Some (U) -> (sc U; true) | None -> false) in  if succeeded then matchConstraint (cnstrSolve, try_ + 1) else () ) in  match I.constStatus (cidFromHead Ha) with (I.Constraint (cs, cnstrSolve)) -> matchConstraint (cnstrSolve, 0) | _ -> matchDProg (dPool, 1) )
let rec solve (gs, dp, sc)  = (T.init (); solve' (gs, dp, sc))
(* local ... *)

 end


(* functor TMachine *)

