Total  Global GLOBAL    Table TABLE   Key Int    Whnf WHNF    Names NAMES    ModeTable MODETABLE    ModeCheck MODECHECK    Index INDEX    Subordinate SUBORDINATE    Order ORDER    Reduces REDUCES    Cover COVER    Origins ORIGINS    Timers TIMERS     TOTAL  struct (*! structure IntSyn = IntSyn' !*)
exception module module module module (* totalTable (a) = SOME() iff a is total, otherwise NONE *)
let  inlet rec reset() clear totalTablelet rec install(cid) insert totalTable (cid,  , ())let rec lookup(cid) lookup totalTable (cid)let rec uninstall(cid) delete totalTable (cid)let  inlet  inlet  inlet rec total(cid) match lookup cid with nONE -> false sOME _ -> trueexception (* copied from terminates/reduces.fun *)
let rec error(c,  , occ,  , msg) (match originLookup c with (fileName,  , nONE) -> raise (error (fileName ^ ":" ^ msg)) (fileName,  , sOME occDec) -> raise (error (wrapLoc' (loc (fileName,  , occToRegionDec occDec occ),  , linesInfoLookup (fileName),  , msg))))(* G is unused here *)
let rec checkDynOrder(g,  , vs,  , 0,  , occ) (if ! chatter >= 5 then print ("Output coverage: skipping redundant checking of third-order clause\n") else (); ()) checkDynOrder(g,  , vs,  , n,  , occ) checkDynOrderW (g,  , whnf vs,  , n,  , occ) checkDynOrderW(g,  , (root _,  , s),  , n,  , occ) () checkDynOrderW(g,  , (pi ((d1 as dec (_,  , v1),  , no),  , v2),  , s),  , n,  , occ) (checkDynOrder (g,  , (v1,  , s),  , n - 1,  , label occ); checkDynOrder (decl (g,  , d1),  , (v2,  , dot1 s),  , n,  , body occ)) checkDynOrderW(g,  , (pi ((d1,  , maybe),  , v2),  , s),  , n,  , occ) checkDynOrder (decl (g,  , d1),  , (v2,  , dot1 s),  , n,  , body occ)(* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for V is satisfied
           for clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: G |- V[s] : type
    *)
let rec checkClause(g,  , vs,  , occ) checkClauseW (g,  , whnf vs,  , occ) checkClauseW(g,  , (pi ((d1,  , maybe),  , v2),  , s),  , occ) let let  in in checkClause (decl (g,  , d1'),  , (v2,  , dot1 s),  , body occ) checkClauseW(g,  , (pi ((d1 as dec (_,  , v1),  , no),  , v2),  , s),  , occ) let let  in in checkGoal (g,  , (v1,  , s),  , label occ) checkClauseW(g,  , (root _,  , s),  , occ) () checkGoal(g,  , vs,  , occ) checkGoalW (g,  , whnf vs,  , occ) checkGoalW(g,  , (v,  , s),  , occ) let let  inlet  inlet  in(* can raise Cover.Error for third-order clauses *)
 in try  with (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)
let rec checkDefinite(a,  , mnil) () checkDefinite(a,  , mapp (marg (plus,  , _),  , ms')) checkDefinite (a,  , ms') checkDefinite(a,  , mapp (marg (minus,  , _),  , ms')) checkDefinite (a,  , ms') checkDefinite(a,  , mapp (marg (star,  , xOpt),  , ms')) error (a,  , top,  , "Error: Totality checking " ^ qidToString (constQid a) ^ ":\n" ^ "All argument modes must be input (+) or output (-)" ^ (match xOpt with nONE -> "" sOME (x) -> " but argument " ^ x ^ " is indefinite (*)"))(* checkOutCover [c1,...,cn] = ()
       iff local output coverage for every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
let rec checkOutCovernil () checkOutCover(const (c) :: cs) (if ! chatter >= 4 then print (qidToString (constQid c) ^ " ") else (); if ! chatter >= 6 then print ("\n") else (); try  with ; checkOutCover cs) checkOutCover(def (d) :: cs) (if ! chatter >= 4 then print (qidToString (constQid d) ^ " ") else (); if ! chatter >= 6 then print ("\n") else (); try  with ; checkOutCover cs)(* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
let rec checkFam(a) let (* Ensuring that there is no bad interaction with type-level definitions *)
let  in(* a cannot be a type-level definition *)
let  in(* Checking termination *)
let  in(* Checking input coverage *)
(* by termination invariant, there must be consistent mode for a *)
let  in(* must be defined and well-moded *)
let  in(* all arguments must be either input or output *)
let  in(* Checking output coverage *)
let  inlet  in(* all variables in output args must be free *)
let  inlet  in in ()end