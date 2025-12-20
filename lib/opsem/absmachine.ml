(* Abstract Machine *)


(* Author: Iliano Cervesato *)


(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)


module AbsMachine (Unify : UNIFY) (Assign : ASSIGN) (Index : INDEX) (CPrint : CPRINT) (Print : PRINT) (Names : NAMES) : ABSMACHINE = struct (*! structure IntSyn = IntSyn' !*)

(*! structure CompSyn = CompSyn' !*)

module I = IntSyn
module C = CompSyn
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
let rec raiseType = function (I.Null, V) -> V | (I.Decl (G, D), V) -> raiseType (G, I.Pi ((D, I.Maybe), V))
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

let rec solve = function ((C.Atom (p), s), dp, sc) -> matchAtom ((p, s), dp, sc) | ((C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc) -> ( let D' = I.Dec (None, I.EClo (A, s)) in  solve ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))), (fun M -> sc (I.Lam (D', M)))) ) | ((C.All (D, g), s), C.DProg (G, dPool), sc) -> ( (*      val D' = I.decSub (D, s) *)
let D' = Names.decLUName (G, I.decSub (D, s)) in  solve ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)), (fun M -> sc (I.Lam (D', M)))) )
and rSolve = function (ps', (C.Eq (Q), s), C.DProg (G, dPool), sc) -> if Unify.unifiable (G, (Q, s), ps')(* effect: instantiate EVars *)
 then sc I.Nil(* call success continuation *)
 else () | (ps', (C.Assign (Q, eqns), s), dp, sc) -> (match Assign.assignable (G, ps', (Q, s)) with Some (cnstr) -> aSolve ((eqns, s), dp, cnstr, (fun () -> sc I.Nil)) | None -> ()) | (ps', (C.And (r, A, g), s), dp, sc) -> ( (* is this EVar redundant? -fp *)
(* same s^-1 *)
let X = I.newEVar (G, I.EClo (A, s)) in  rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp, (fun S -> solve ((g, s), dp, (fun M -> sc (I.App (M, S)))))) ) | (ps', (C.Exists (I.Dec (_, A), r), s), dp, sc) -> ( let X = I.newEVar (G, I.EClo (A, s)) in  rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp, (fun S -> sc (I.App (X, S)))) ) | (ps', (C.Axists (I.ADec (_, d), r), s), dp, sc) -> ( let X' = I.newAVar () in  rSolve (ps', (r, I.Dot (I.Exp (I.EClo (X', I.Shift (~ d))), s)), dp, sc)(* we don't increase the proof term here! *)
 )
and aSolve = function ((C.Trivial, s), dp, cnstr, sc) -> if Assign.solveCnstr cnstr then sc () else () | ((C.UnifyEq (G', e1, N, eqns), s), dp, cnstr, sc) -> ( let G'' = compose (G, G') in let s' = shiftSub (G', s) in  if Assign.unifiable (G'', (N, s'), (e1, s')) then aSolve ((eqns, s), dp, cnstr, sc) else () )
and matchAtom (ps', dp, sc)  = ( (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for_sml solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
(* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for_sml solving atomic goal ps', starting
           with c1.

           succeeds exactly once (#succeeds = 1)
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for_sml solving atomic goal ps', starting
           with the most recent one.
        *)
let deterministic = C.detTableCheck (cidFromHead Ha) in exception SucceedOnce of I.spine in let rec matchSig = function [] -> () | (Hc :: sgn') -> ( let C.SClause (r) = C.sProgLookup (cidFromHead Hc) in  (* trail to undo EVar instantiations *)
CSManager.trail (fun () -> rSolve (ps', (r, I.id), dp, (fun S -> sc (I.Root (Hc, S))))); matchSig sgn' ) in let rec matchSigDet = function [] -> () | (Hc :: sgn') -> ( let C.SClause (r) = C.sProgLookup (cidFromHead Hc) in  (* trail to undo EVar instantiations *)
try (CSManager.trail (fun () -> (rSolve (ps', (r, I.id), dp, (fun S -> raise (SucceedOnce S))))); matchSigDet sgn') with SucceedOnce S -> sc (I.Root (Hc, S)) ) in let rec matchDProg = function (I.Null, _) -> if deterministic then matchSigDet (Index.lookup (cidFromHead Ha)) else matchSig (Index.lookup (cidFromHead Ha)) | (I.Decl (dPool', C.Dec (r, s, Ha')), k) -> if eqHead (Ha, Ha') then if deterministic then (* #succeeds = 1 *)
(try (CSManager.trail (* trail to undo EVar instantiations *)
 (fun () -> rSolve (ps', (r, I.comp (s, I.Shift (k))), dp, (fun S -> (raise (SucceedOnce S))))); matchDProg (dPool', k + 1)) with SucceedOnce S -> sc (I.Root (I.BVar (k), S))) else (* #succeeds >= 1 -- allows backtracking *)
(CSManager.trail (* trail to undo EVar instantiations *)
 (fun () -> rSolve (ps', (r, I.comp (s, I.Shift (k))), dp, (fun S -> sc (I.Root (I.BVar (k), S))))); matchDProg (dPool', k + 1)) else matchDProg (dPool', k + 1) | (I.Decl (dPool', C.Parameter), k) -> matchDProg (dPool', k + 1) in let rec matchConstraint (cnstrSolve, try_)  = ( let succeeded = CSManager.trail (fun () -> match (cnstrSolve (G, I.SClo (S, s), try_)) with Some (U) -> (sc U; true) | None -> false) in  if succeeded then matchConstraint (cnstrSolve, try_ + 1) else () ) in  match I.constStatus (cidFromHead Ha) with (I.Constraint (cs, cnstrSolve)) -> matchConstraint (cnstrSolve, 0) | _ -> matchDProg (dPool, 1) )
let solve = solve
(* local ... *)

 end


(* functor AbsMachine *)

