PtRecon  Unify UNIFY    Assign ASSIGN    MemoTable MEMOTABLE    Index INDEX    CPrint CPRINT    Names NAMES     PTRECON  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
(*! structure TableParam = TableParam !*)
module module module exception let rec cidFromHead(const a) a cidFromHead(def a) alet rec eqHead(const a,  , const a') a = a' eqHead(def a,  , def a') a = a' eqHead_ falselet rec compose'(null,  , g) g compose'(decl (g,  , d),  , g') decl (compose' (g,  , g'),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))(* We write
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
let rec solve'(o,  , (atom (p),  , s),  , dp as dProg (g,  , dPool),  , sc) matchAtom (o,  , (p,  , s),  , dp,  , sc) solve'(o,  , (impl (r,  , a,  , ha,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  in in if (! strengthen) then (match memberCtx ((g,  , eClo (a,  , s)),  , g) with sOME (d) -> let let  in in (* need to reuse label for this assumption .... *)
solve' (o,  , (g,  , dot (exp (x),  , s)),  , dProg (g,  , dPool),  , (fun (o,  , m) -> sc (o,  , lam (d',  , m)))) nONE -> solve' (o,  , (g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (fun (o,  , m) -> sc (o,  , lam (d',  , m))))) else solve' (o,  , (g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (fun (o,  , m) -> sc (o,  , (lam (d',  , m)))))(*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*)
 solve'(o,  , (all (d,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  in(* val D' = I.decSub (D, s) *)
 in solve' (o,  , (g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , (fun (o,  , m) -> sc (o,  , (lam (d',  , m)))))(* rsolve (O, (p,s'), (r,s), dp, sc) = ()
     Invariants:
       O = oracle
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
 rSolve(o,  , ps',  , (eq (q),  , s),  , dProg (g,  , dPool),  , sc) if unifiable (g,  , (q,  , s),  , ps')(* effect: instantiate EVars *)
 then sc (o,  , nil)(* call success continuation *)
 else (let let  in in ()) rSolve(o,  , ps',  , (assign (q,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , sc) (match assignable (g,  , ps',  , (q,  , s)) with sOME (cnstr) -> if aSolve ((eqns,  , s),  , dp,  , cnstr) then sc (o,  , nil) else print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n" nONE -> print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n") rSolve(o,  , ps',  , (and (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , sc) let (* is this EVar redundant? -fp *)
let  in in rSolve (o,  , ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun (o,  , s) -> solve' (o,  , (g,  , s),  , dp,  , (fun (o,  , m) -> sc (o,  , (app (m,  , s))))))) rSolve(o,  , ps',  , (exists (dec (_,  , a),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  in in rSolve (o,  , ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun (o,  , s) -> sc (o,  , (app (x,  , s))))) rSolve(o,  , ps',  , (axists (aDec (sOME (x),  , d),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  in in rSolve (o,  , ps',  , (r,  , dot (exp (eClo (x',  , shift (~ d))),  , s)),  , dp,  , sc)(* we don't increase the proof term here! *)
(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
 aSolve((trivial,  , s),  , dp,  , cnstr) solveCnstr cnstr aSolve((unifyEq (g',  , e1,  , n,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , cnstr) let let  inlet  in in unifiable (g'',  , (n,  , s'),  , (e1,  , s')) && aSolve ((eqns,  , s),  , dp,  , cnstr)(* matchatom (O, (p, s), dp, sc) => ()
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
 matchAtom((ho :: o),  , ps' as (root (ha,  , s),  , s),  , dp as dProg (g,  , dPool),  , sc) let (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
let rec matchSig(nil,  , k) raise (error (" \noracle #Pc does not exist \n")) matchSig(((hc as (const c)) :: sgn'),  , k) if c = k then let let  in in rSolve (o,  , ps',  , (r,  , id),  , dp,  , (fun (o,  , s) -> sc (o,  , (root (hc,  , s))))) else matchSig (sgn',  , k) matchSig(((hc as (def d)) :: sgn'),  , k) if d = k then let let  in in rSolve (o,  , ps',  , (r,  , id),  , dp,  , (fun (o,  , s) -> sc (o,  , (root (hc,  , s))))) else matchSig (sgn',  , k)(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
let rec matchDProg(null,  , i,  , k) raise (error ("\n selected dynamic clause number does not exist in current dynamic clause pool!\n")) matchDProg(decl (dPool',  , dec (r,  , s,  , ha')),  , 1,  , k) if eqHead (ha,  , ha') then rSolve (o,  , ps',  , (r,  , comp (s,  , shift (k))),  , dp,  , (fun (o,  , s) -> sc (o,  , (root (bVar (k),  , s))))) else (* shouldn't happen *)
raise (error ("\n selected dynamic clause does not match current goal!\n")) matchDProg(decl (dPool',  , dc),  , i,  , k) matchDProg (dPool',  , i - 1,  , k) in (match ho with pc i -> matchSig (lookup (cidFromHead ha),  , i) dc i -> matchDProg (dPool,  , i,  , i) csolver u -> sc (o,  , u))let rec solve(o,  , (g,  , s),  , dp as dProg (g,  , dPool),  , sc) try  with (* local ... *)
end