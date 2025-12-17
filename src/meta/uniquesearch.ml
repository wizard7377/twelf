UniqueSearch  Global GLOBAL    StateSyn' STATESYN    Abstract ABSTRACT    MTPGlobal MTPGLOBAL    Whnf WHNF    Unify UNIFY    Assign ASSIGN    Index INDEX    Compile COMPILE    CPrint CPRINT    Print PRINT    Names NAMES     UNIQUESEARCH  struct (*! structure IntSyn = IntSyn' !*)
(*! structure FunSyn = FunSyn' !*)
module (*! structure CompSyn = CompSyn' !*)
exception type Acctypemodule module (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)
let rec isInstantiated(root (const (cid),  , _)) true isInstantiated(pi (_,  , v)) isInstantiated v isInstantiated(root (def (cid),  , _)) true isInstantiated(redex (v,  , s)) isInstantiated v isInstantiated(lam (_,  , v)) isInstantiated v isInstantiated(eVar (ref (sOME (v)),  , _,  , _,  , _)) isInstantiated v isInstantiated(eClo (v,  , s)) isInstantiated v isInstantiated_ falselet rec compose'(null,  , g) g compose'(decl (g,  , d),  , g') decl (compose' (g,  , g'),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))(* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
let rec existspk let let rec exists'(null) false exists'(decl (k',  , y)) p (y) || exists' (k') in exists' k(* occursInExp (r, (U, s)) = B,

       Invariant:
       If    G |- s : G1   G1 |- U : V
       then  B holds iff r occurs in (the normal form of) U
    *)
let rec occursInExp(r,  , vs) occursInExpW (r,  , whnf vs) occursInExpW(r,  , (uni _,  , _)) false occursInExpW(r,  , (pi ((d,  , _),  , v),  , s)) occursInDec (r,  , (d,  , s)) || occursInExp (r,  , (v,  , dot1 s)) occursInExpW(r,  , (root (_,  , s),  , s)) occursInSpine (r,  , (s,  , s)) occursInExpW(r,  , (lam (d,  , v),  , s)) occursInDec (r,  , (d,  , s)) || occursInExp (r,  , (v,  , dot1 s)) occursInExpW(r,  , (eVar (r',  , _,  , v',  , _),  , s)) (r = r') || occursInExp (r,  , (v',  , s)) occursInExpW(r,  , (fgnExp csfe,  , s)) fold csfe (fun (u,  , b) -> b || occursInExp (r,  , (u,  , s))) false(* hack - should consult cs  -rv *)
 occursInSpine(_,  , (nil,  , _)) false occursInSpine(r,  , (sClo (s,  , s'),  , s)) occursInSpine (r,  , (s,  , comp (s',  , s))) occursInSpine(r,  , (app (u,  , s),  , s)) occursInExp (r,  , (u,  , s)) || occursInSpine (r,  , (s,  , s)) occursInDec(r,  , (dec (_,  , v),  , s)) occursInExp (r,  , (v,  , s))(* nonIndex (r, GE) = B

       Invariant:
       B hold iff
        r does not occur in any type of EVars in GE
    *)
let rec nonIndex(_,  , nil) true nonIndex(r,  , eVar (_,  , _,  , v,  , _) :: gE) (not (occursInExp (r,  , (v,  , id)))) && nonIndex (r,  , gE)(* select (GE, (V, s), acc) = acc'

       Invariant:
    *)
(* Efficiency: repeated whnf for every subterm in Vs!!! *)
let rec selectEVar(nil) nil selectEVar((x as eVar (r,  , _,  , _,  , ref nil)) :: gE) let let  in in if nonIndex (r,  , xs) then xs @ [x] else xs selectEVar((x as eVar (r,  , _,  , _,  , cnstrs)) :: gE) let let  in in if nonIndex (r,  , xs) then x :: xs else xs(* pruneCtx (G, n) = G'

       Invariant:
       If   |- G ctx
       and  G = G0, G1
       and  |G1| = n
       then |- G' = G0 ctx
    *)
let rec pruneCtx(g,  , 0) g pruneCtx(decl (g,  , _),  , n) pruneCtx (g,  , n - 1)let rec cidFromHead(const a) a cidFromHead(def a) a cidFromHead(skonst a) a(* only used for type families of compiled clauses *)
let rec eqHead(const a,  , const a') a = a' eqHead(def a,  , def a') a = a' eqHead_ false(* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)
let rec solve(max,  , depth,  , (atom p,  , s),  , dp,  , sc,  , acc) matchAtom (max,  , depth,  , (p,  , s),  , dp,  , sc,  , acc) solve(max,  , depth,  , (impl (r,  , a,  , h,  , g),  , s),  , dProg (g,  , dPool),  , sc,  , acc) let let  in in solve (max,  , depth + 1,  , (g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , h))),  , (fun (m,  , acc') -> sc (lam (d',  , m),  , acc')),  , acc) solve(max,  , depth,  , (all (d,  , g),  , s),  , dProg (g,  , dPool),  , sc,  , acc) let let  in in solve (max,  , depth + 1,  , (g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , (fun (m,  , acc') -> sc (lam (d',  , m),  , acc')),  , acc)(* rsolve (max, depth, (p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
     Invariants:
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       G ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit
           (used in the existential case for iterative deepening,
            used in the universal case for max search depth)
       if G |- S :: r[s] then G |- sc : (r >> p[s']) => Answer
  *)
 rSolve(max,  , depth,  , ps',  , (eq q,  , s),  , dProg (g,  , dPool),  , sc,  , acc) if unifiable (g,  , ps',  , (q,  , s)) then sc (nil,  , acc) else acc rSolve(max,  , depth,  , ps',  , (assign (q,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acc) (match assignable (g,  , ps',  , (q,  , s)) with sOME (cnstr) -> aSolve ((eqns,  , s),  , dp,  , cnstr,  , (fun () -> sc (nil,  , acc)),  , acc) nONE -> acc) rSolve(max,  , depth,  , ps',  , (and (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acc) let (* is this EVar redundant? -fp *)
let  in in rSolve (max,  , depth,  , ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun (s,  , acc') -> solve (max,  , depth,  , (g,  , s),  , dp,  , (fun (m,  , acc'') -> sc (app (m,  , s),  , acc'')),  , acc')),  , acc) rSolve(max,  , depth,  , ps',  , (in (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acc) let (* G |- g goal *)
(* G |- A : type *)
(* G, A |- r resgoal *)
(* G0, Gl  |- s : G *)
let  inlet  inlet  in(* G0, Gl  |- w : G0 *)
let  in(* G0 |- iw : G0, Gl *)
let  in(* G0 |- w : G *)
let  in(* G0 |- X : A[s'] *)
let  in(* G0, Gl |- X' : A[s'][w] = A[s] *)
 in rSolve (max,  , depth,  , ps',  , (r,  , dot (exp (x'),  , s)),  , dp,  , (fun (s,  , acc') -> if isInstantiated x then sc (app (x',  , s),  , acc') else solve (max,  , 0,  , (g,  , s'),  , dProg (g0,  , dPool0),  , (fun (m,  , acc'') -> (try  with )),  , acc')),  , acc) rSolve(max,  , depth,  , ps',  , (exists (dec (_,  , a),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acc) let let  in in rSolve (max,  , depth,  , ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun (s,  , acc') -> sc (app (x,  , s),  , acc')),  , acc) rSolve(max,  , depth,  , ps',  , (axists (aDec (sOME (x),  , d),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc,  , acc) let let  in in rSolve (max,  , depth,  , ps',  , (r,  , dot (exp (eClo (x',  , shift (~ d))),  , s)),  , dp,  , sc,  , acc)(* we don't increase the proof term here! *)
(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
 aSolve((trivial,  , s),  , dp,  , cnstr,  , sc,  , acc) (if solveCnstr cnstr then sc () else acc) aSolve((unifyEq (g',  , e1,  , n,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , cnstr,  , sc,  , acc) let let  inlet  in in if unifiable (g'',  , (n,  , s'),  , (e1,  , s')) then aSolve ((eqns,  , s),  , dp,  , cnstr,  , sc,  , acc) else acc(* matchatom ((p, s), (G, dPool), sc, (acc, k)) => ()
     G |- s : G'
     G' |- p :: atom
     G ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if G |- M :: p[s] then G |- sc :: p[s] => Answer
  *)
 matchAtom(0,  , _,  , _,  , _,  , _,  , acc) acc matchAtom(max,  , depth,  , ps' as (root (ha,  , _),  , _),  , dp as dProg (g,  , dPool),  , sc,  , acc) let let rec matchSig'(nil,  , acc') acc' matchSig'(hc :: sgn',  , acc') let let  inlet  in in matchSig' (sgn',  , acc''')let rec matchDProg(null,  , _,  , acc') matchSig' (lookup (cidFromHead ha),  , acc') matchDProg(decl (dPool',  , dec (r,  , s,  , ha')),  , n,  , acc') if eqHead (ha,  , ha') then let let  in in matchDProg (dPool',  , n + 1,  , acc''') else matchDProg (dPool',  , n + 1,  , acc') matchDProg(decl (dPool',  , parameter),  , n,  , acc') matchDProg (dPool',  , n + 1,  , acc') in matchDProg (dPool,  , 1,  , acc)(* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
(* contexts of EVars are recompiled for each search depth *)
 searchEx'max(nil,  , sc,  , acc) sc acc searchEx'max((x as eVar (r,  , g,  , v,  , _)) :: gE,  , sc,  , acc) solve (max,  , 0,  , (compileGoal (g,  , v),  , id),  , compileCtx false g,  , (fun (u',  , acc') -> try  with ),  , acc)(* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
         where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
         been instantiated
       then acc' is a list containing the one result from executing the success continuation
         All EVar's got instantiated with the smallest possible terms.
    *)
let rec searchEx(it,  , depth)(gE,  , sc,  , acc) (if ! chatter > 5 then print "[Search: " else (); searchEx' depth (selectEVar (gE),  , fun acc' -> (if ! chatter > 5 then print "OK]\n" else (); let let  inlet  in in if gE' > 0 then if it > 0 then searchEx (it - 1,  , depth) (gE',  , sc,  , acc') else raise (error "not found") else sc acc'(* warning: iterative deepening depth is not propably updated.
                                             possible that it runs into an endless loop ? *)
),  , acc))(* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit

       Side effect:
       success continuation will raise exception
    *)
(* Shared contexts of EVars in GE may recompiled many times *)
let rec search(maxFill,  , gE,  , sc) searchEx (1,  , maxFill) (gE,  , sc,  , nil)let  in(* local ... *)
end