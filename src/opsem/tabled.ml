Tabled  Unify UNIFY    TabledSyn TABLEDSYN    Assign ASSIGN    Index INDEX    Queue QUEUE    AbstractTabled ABSTRACTTABLED    MemoTable MEMOTABLE    CPrint CPRINT    Print PRINT     TABLED  struct (*! structure IntSyn = IntSyn' !*)
(*! structure CompSyn = CompSyn' !*)
module module (*! structure TableParam = TableParam !*)
(*  structure Match = Match*)
module module module module module (* ---------------------------------------------------------------------- *)
(* Suspended goal: SuspType, s, G, sc, ftrail, answerRef, i

       where
       s is a substitution for the existential variables in D such that G |- s : G, D
       sc        : is the success continuation
       ftrail    : is a forward trail
       answerRef : pointer to potential answers in the memo-table
       i         : Number of answer which already have been consumed  by this
                   current program state

    *)
type SuspTypelet  inexception (* ---------------------------------------------------------------------- *)
let rec cidFromHead(const a) a cidFromHead(def a) alet rec eqHead(const a,  , const a') a = a' eqHead(def a,  , def a') a = a' eqHead_ falselet rec append(null,  , g) g append(decl (g',  , d),  , g) decl (append (g',  , g),  , d)let rec shift(null,  , s) s shift(decl (g,  , d),  , s) dot1 (shift (g,  , s))let rec raiseType(null,  , v) v raiseType(decl (g,  , d),  , v) raiseType (g,  , lam (d,  , v))let rec compose(null,  , g) g compose(decl (g,  , d),  , g') decl (compose (g,  , g'),  , d)(* ---------------------------------------------------------------------- *)
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
(* ---------------------------------------------------------------------- *)
(* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
let rec ctxToEVarSub(null,  , s) s ctxToEVarSub(decl (g,  , dec (_,  , a)),  , s) let let  in in dot (exp (x),  , ctxToEVarSub (g,  , s))let rec ctxToAVarSub(null,  , s) s ctxToAVarSub(decl (g,  , dec (_,  , a)),  , s) let let  in in dot (exp (x),  , ctxToAVarSub (g,  , s)) ctxToAVarSub(decl (g,  , aDec (_,  , d)),  , s) let let  in in dot (exp (eClo (x,  , shift (~ d))),  , ctxToAVarSub (g,  , s))(* ---------------------------------------------------------------------- *)
(* Solving  variable definitions *)
(* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G  . |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
let rec solveEqn((trivial,  , s),  , g) true solveEqn((unify (g',  , e1,  , n,  , eqns),  , s),  , g) let let  inlet  in(* G, G' |- s' : D, G, G' *)
 in unifiable (g'',  , (n,  , s'),  , (e1,  , s')) && solveEqn ((eqns,  , s),  , g)let rec unifySub'(g,  , s1,  , s2) try  with let rec unify(g,  , us,  , us') try  with let rec getHypGoal(dProg,  , (atom p,  , s)) (dProg,  , (p,  , s)) getHypGoal(dProg (g,  , dPool),  , (impl (r,  , a,  , ha,  , g),  , s)) let let  in in if (! strengthen) then (match memberCtx ((g,  , eClo (a,  , s)),  , g) with sOME (_) -> (let let  in(* is g always atomic? *)
let  in in getHypGoal (dProg (g,  , dPool),  , (g,  , dot (exp (x),  , s)))) nONE -> getHypGoal (dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (g,  , dot1 s))) else getHypGoal (dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (g,  , dot1 s)) getHypGoal(dProg (g,  , dPool),  , (all (d,  , g),  , s)) let let  in in getHypGoal (dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , (g,  , dot1 s))let rec updateGlobalTable(goal,  , flag) let let  inlet  inlet  inlet  in in if keepTable (targetFam u') then match callCheck (dAVars,  , dEVars,  , g',  , u',  , eqn',  , status) with repeatedEntry (_,  , answRef,  , _) -> (globalTable := ((dAVars,  , dEVars,  , g',  , u',  , eqn',  , answRef,  , status) :: (! globalTable))) _ -> raise (error "Top level goal should always in the table\n") else ()let rec keepTablec keepTable clet rec fillTable() let let rec insert(nil) () insert((dAVars,  , dEVars,  , g',  , u',  , eqn',  , answRef,  , status) :: t) match insertIntoTree (dAVars,  , dEVars,  , g',  , u',  , eqn',  , answRef,  , status) with newEntry (_) -> insert t _ -> () in insert (! globalTable)(*------------------------------------------------------------------------------------------*)
(* retrieve' ((G, U, s), asub, AnswerList, sc) = ()

     retrieval for subsumption must take into account the asub substitution

     Invariants:
     if
       Goal:                        Answer substitution from index:
       D   |- Pi G. U
       .   |- s : D        and      D' |- s1 : D1
       D   |- asub : D1    and      .  |- s1' : D' (reinstantiate evars)

                                scomp = s1 o s1'
                                  .  |- scomp : D1

       .  |- [esub]asub : D1  where
       .  |- esub : D      and  G |- esub^|G| : D , G
       .  |- s : D         and  G |- s^|G| : D, G
     then
       unify (G, esub^|G|, s^|G|) and unify (G, ([esub]asub)^|G|, scomp^|G|)
       if unification succeeds
         then we continue solving the success continuation.
         otherwise we fail

     Effects: instantiation of EVars in s, s1' and esub
     any effect  sc O1  might have

   *)
let rec retrieve'((g,  , u,  , s),  , asub,  , [],  , sc) () retrieve'((g,  , u,  , s),  , (esub,  , asub),  , (((d',  , s1),  , o1) :: a),  , sc) let let  inlet  inlet  inlet  inlet  inlet  inlet  in in trail (fun () -> if (unifySub' (g,  , shift (g,  , esub),  , ss) && unifySub' (g,  , shift (g,  , comp (asub,  , esub)),  , ss1)) then (sc o1)(* Succeed *)
 else ())(* Fail *)
retrieve' ((g,  , u,  , s),  , (esub,  , asub),  , a,  , sc)(* currently not used -- however, it may be better to not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
(* retrieveV ((G, U, s), answerList, sc)
      if
        . |- [s]Pi G.U
        . |- s : DAVars, DEVars

        ((DEVars_i, s_i), O_i) is an element in answer list
         DEVars_i |- s_i : DAVars, DEVars
         and O_i is a proof skeleton
      then
        sc O_i is evaluated
        Effects: instantiation of EVars in s

   *)
let rec retrieveV((g,  , u,  , s),  , [],  , sc) () retrieveV((g,  , u,  , s),  , (((dEVars,  , s1),  , o1) :: a),  , sc) let let  inlet  inlet  inlet  in(* for subsumption we must combine it with asumb!!! *)
 in trail (fun () -> if unifySub' (g,  , ss,  , ss1) then (sc o1) else ())retrieveV ((g,  , u,  , s),  , a,  , sc)let rec retrieveSW((g,  , u,  , s),  , asub,  , answL,  , sc) retrieve' ((g,  , u,  , s),  , asub,  , answL,  , sc)(* currently not used -- however, it may be better to  not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
(* fun retrieveSW ((G, U, s), asub, AnswL, sc) =
     case (!TableParam.strategy) of
       TableParam.Variant =>  retrieveV ((G, U, s), AnswL, sc)
     | TableParam.Subsumption => retrieve' ((G, U, s), asub, AnswL, sc) *)
(* retrieve (k, (G, s), (asub, answRef), sc) = ()
      Invariants:
      If
         G |-   s : G, D   where s contains free existential variables defined in D
         answRef is a pointer to the AnswerList

        G |- asub : D, G  asub is the identity in the variant case
        G |- asub : D, G  asub instantiates existential variables in s.

     then the success continuation sc is triggered.

     Effects: instantiation of EVars in s, and asub
   *)
let rec retrieve(k,  , (g,  , u,  , s),  , (asub,  , answRef),  , sc) let let  inlet  inlet  in in k := lkpretrieveSW ((g,  , u,  , s),  , asub,  , answ',  , sc)(* ---------------------------------------------------------------------- *)
(* solve ((g, s), dp, sc) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- g  goal
     if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
     any effect  sc M  might have
     *)
let rec solve((atom (p),  , s),  , dp as dProg (g,  , dPool),  , sc) if tabledLookup (targetFam p) then let let  in(* Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *)
let  in in match callCheck (dAVars,  , dEVars,  , g',  , u',  , eqn',  , incomplete)(* Side effect: D', G' |- U' added to table *)
 with newEntry (answRef) -> matchAtom ((p,  , s),  , dp,  , (fun pskeleton -> match answerCheck (s',  , answRef,  , pskeleton) with repeated -> () new -> (sc pskeleton))) repeatedEntry (asub,  , answRef,  , incomplete) -> if noAnswers answRef then (* loop detected
                  * NOTE: we might suspend goals more than once.
                  *     example: answer list for goal (p,s) is saturated
                  *              but not the whole table is saturated.
                  *)
(suspGoals := ((loop,  , (g',  , u',  , s'),  , sc,  , suspend (),  , (asub,  , answRef),  , ref 0) :: (! suspGoals)); ()) else (* loop detected
                  * new answers available from previous stages
                  * resolve current goal with all possible answers
                  *)
let let  in in suspGoals := ((loop,  , (g',  , u',  , s'),  , sc,  , suspend (),  , (asub,  , answRef),  , ref le) :: (! suspGoals))retrieve (ref 0,  , (g',  , u',  , s'),  , (asub,  , answRef),  , sc) repeatedEntry (asub,  , answRef,  , complete) -> if noAnswers answRef then (* Subgoal is not provable *)
() else (* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *)
retrieve (ref 0,  , (g',  , u',  , s'),  , (asub,  , answRef),  , sc) divergingEntry (asub,  , answRef) -> (* loop detected  -- currently not functioning correctly.
                    we might be using this as part of a debugger which suggests diverging goals
                    to the user so the user can prove a generalized goal first.
                    Wed Dec 22 08:27:24 2004 -bp
                  *)
(suspGoals := ((divergence ((p,  , s),  , dp),  , (g',  , u',  , s'),  , sc,  , suspend (),  , ((id, (* this is a hack *)
,  , asub),  , answRef),  , ref 0) :: (! suspGoals)); ()) else matchAtom ((p,  , s),  , dp,  , sc) solve((impl (r,  , a,  , ha,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  in in if (! strengthen) then (match memberCtx ((g,  , eClo (a,  , s)),  , g) with sOME (_) -> (let let  in in solve ((g,  , dot (exp (x),  , s)),  , dProg (g,  , dPool),  , (fun o -> sc o))) nONE -> solve ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (fun o -> sc o))) else solve ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , dec (r,  , s,  , ha))),  , (fun o -> sc o)) solve((all (d,  , g),  , s),  , dProg (g,  , dPool),  , sc) let let  in in solve ((g,  , dot1 s),  , dProg (decl (g,  , d'),  , decl (dPool,  , parameter)),  , (fun o -> sc o))(* rsolve ((p,s'), (r,s), dp, sc) = ()
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
 rSolve(ps',  , (eq (q),  , s),  , dProg (g,  , dPool),  , sc) (if unifiable (g,  , ps',  , (q,  , s))(* effect: instantiate EVars *)
 then sc [](* call success continuation *)
 else ()) rSolve(ps',  , (assign (q,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , sc) (match assignable (g,  , ps',  , (q,  , s)) with sOME (cnstr) -> aSolve ((eqns,  , s),  , dp,  , cnstr,  , (fun s -> sc s)) nONE -> ()) rSolve(ps',  , (and (r,  , a,  , g),  , s),  , dp as dProg (g,  , dPool),  , sc) let (* is this EVar redundant? -fp *)
let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun s1 -> solve ((g,  , s),  , dp,  , (fun s2 -> sc (s1 @ s2))))) rSolve(ps',  , (exists (dec (_,  , a),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  in in rSolve (ps',  , (r,  , dot (exp (x),  , s)),  , dp,  , (fun s -> sc s)) rSolve(ps',  , (axists (aDec (sOME (x),  , d),  , r),  , s),  , dp as dProg (g,  , dPool),  , sc) let let  in in rSolve (ps',  , (r,  , dot (exp (eClo (x',  , shift (~ d))),  , s)),  , dp,  , sc)(* we don't increase the proof term here! *)
(* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)
 aSolve((trivial,  , s),  , dp,  , cnstr,  , sc) (if solveCnstr cnstr then (sc []) else ()) aSolve((unifyEq (g',  , e1,  , n,  , eqns),  , s),  , dp as dProg (g,  , dPool),  , cnstr,  , sc) let let  inlet  in in if unifiable (g'',  , (n,  , s'),  , (e1,  , s')) then aSolve ((eqns,  , s),  , dp,  , cnstr,  , sc) else ()(* matchatom ((p, s), dp, sc) => ()
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
 matchAtom(ps' as (root (ha,  , s),  , s),  , dp as dProg (g,  , dPool),  , sc) let (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
let rec matchSignil () matchSig((hc as const c) :: sgn') let let  in in (* trail to undo EVar instantiations *)
trail (fun () -> rSolve (ps',  , (r,  , id),  , dp,  , (fun s -> sc ((pc c) :: s))))matchSig sgn'(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
let rec matchDProg(null,  , null,  , _) matchSig (lookup (cidFromHead ha)) matchDProg(decl (g,  , _),  , decl (dPool',  , dec (r,  , s,  , ha')),  , k) if eqHead (ha,  , ha') then (* trail to undo EVar instantiations *)
(trail (fun () -> rSolve (ps',  , (r,  , comp (s,  , shift (k))),  , dp,  , (fun s -> sc ((dc k) :: s)))); matchDProg (g,  , dPool',  , k + 1)) else matchDProg (g,  , dPool',  , k + 1) matchDProg(decl (g,  , _),  , decl (dPool',  , parameter),  , k) matchDProg (g,  , dPool',  , k + 1)let rec matchConstraint(solve,  , try) let let  in in if succeeded then matchConstraint (solve,  , try + 1) else () in match constStatus (cidFromHead ha) with (constraint (cs,  , solve)) -> matchConstraint (solve,  , 0) _ -> matchDProg (g,  , dPool,  , 1)(* retrieval ((p, s), dp, sc, answRef, n) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- p  goal
     answRef : pointer to corresponding answer list
     n       : #number of answers which were already consumed
               by the current goal

     if answers are available
      then retrieve all new answers
     else fail
     *)
let rec retrieval(loop,  , (g',  , u',  , s'),  , sc,  , (asub,  , answRef),  , n) if noAnswers answRef then (* still  no answers available from previous stages *)
(* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
() else (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *)
retrieve (n,  , (g',  , u',  , s'),  , (asub,  , answRef),  , sc) retrieval(divergence ((p,  , s),  , dp),  , (g',  , u',  , s'),  , sc,  , (asub,  , answRef),  , n) matchAtom ((p,  , s),  , dp,  , (fun pskeleton -> match answerCheck (s',  , answRef,  , pskeleton) with repeated -> () new -> sc pskeleton))let rec tableSize() tableSize ()let rec suspGoalNo() length (! suspGoals)(*  nextStage () = bool
     Side effect: advances lookup pointers
   *)
let rec nextStage() let let rec resume[] () resume(((susp,  , s,  , sc,  , trail,  , (asub,  , answRef),  , k) :: goals)) (trail (fun () -> (resume trail; retrieval (susp,  , s,  , sc,  , (asub,  , answRef),  , k))); resume (goals))let  in in if updateTable () then (* table changed during previous stage *)
(stageCtr := (! stageCtr) + 1; resume (sG); true) else (* table did not change during previous stage *)
falselet rec reset() (suspGoals := []; reset (); stageCtr := 0)let rec solveQuery((g,  , s),  , dp as dProg (g,  , dPool),  , sc) solve ((g,  , s),  , dp,  , sc)(* local ... *)
let  inend