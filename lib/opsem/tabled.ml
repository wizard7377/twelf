(* Tabled Abstract Machine      *)

(* Author: Brigitte Pientka     *)

module type TABLED = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure CompSyn : Compsyn.COMPSYN !*)
  val solve :
    (CompSyn.goal * IntSyn.sub) * CompSyn.dProg * (CompSyn.pskeleton -> unit) ->
    unit

  val updateGlobalTable : CompSyn.goal * bool -> unit
  val keepTable : IntSyn.cid -> bool
  val fillTable : unit -> unit
  val nextStage : unit -> bool
  val reset : unit -> unit
  val tableSize : unit -> int
  val suspGoalNo : unit -> int
end

(* signature Table.TABLED *)
(* Abstract Machine for_sml tabling*)


(* Author: Brigitte Pientka *)


(* Based on abstract machine in absmachine.fun *)


module Tabled (Unify : Unify.UNIFY) (TabledSyn : Table.Tabledsyn.TABLEDSYN) (Assign : Assign.ASSIGN) (Index : Index.INDEX) (Queue : Queue.QUEUE) (AbstractTabled : Abstract.Abstract.ABSTRACTTABLED) (MemoTable : Subtree.Sw_subtree.MEMOTABLE) (CPrint : Cprint.CPRINT) (Print : Print.PRINT) : Table.TABLED = struct (*! structure IntSyn = IntSyn' !*)

(*! structure CompSyn = CompSyn' !*)

module Unify = Unify
module TabledSyn = TabledSyn
(*! structure TableParam = TableParam !*)

(*  structure Match = Match*)

module I = IntSyn
module C = CompSyn
module A = AbstractTabled
module T = TableParam
module MT = MemoTable
(* ---------------------------------------------------------------------- *)

(* Suspended goal: SuspType, s, G, sc, ftrail, answerRef, i

       where
       s is a substitution for_sml the existential variables in D such that G |- s : G, D
       sc        : is the success continuation
       ftrail    : is a forward trail
       answerRef : pointer to potential answers in the memo-table
       i         : Number of answer which already have been consumed  by this
                   current program state

    *)

type suspType = Loop | Divergence of ((IntSyn.exp * IntSyn.sub) * CompSyn.dProg)
let SuspGoals : suspType * (IntSyn.dctx * IntSyn.exp * IntSyn.sub) * (CompSyn.pskeleton -> unit) * Unify.unifTrail * ((IntSyn.sub * IntSyn.sub) * T.answer) * int ref list ref = ref []
exception Error of string
(* ---------------------------------------------------------------------- *)

let rec cidFromHead = function (I.Const a) -> a | (I.Def a) -> a
let rec eqHead = function (I.Const a, I.Const a') -> a = a' | (I.Def a, I.Def a') -> a = a' | _ -> false
let rec append = function (IntSyn.Null, G) -> G | (IntSyn.Decl (G', D), G) -> IntSyn.Decl (append (G', G), D)
let rec shift = function (IntSyn.Null, s) -> s | (IntSyn.Decl (G, D), s) -> I.dot1 (shift (G, s))
let rec raiseType = function (I.Null, V) -> V | (I.Decl (G, D), V) -> raiseType (G, I.Lam (D, V))
let rec compose = function (IntSyn.Null, G) -> G | (IntSyn.Decl (G, D), G') -> IntSyn.Decl (compose (G, G'), D)
(* ---------------------------------------------------------------------- *)

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

(* ---------------------------------------------------------------------- *)

(* ctxToEVarSub D = s

     if D is a context for_sml existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)

let rec ctxToEVarSub = function (I.Null, s) -> s | (I.Decl (G, I.Dec (_, A)), s) -> ( let X = I.newEVar (I.Null, A) in  I.Dot (I.Exp (X), ctxToEVarSub (G, s)) )
let rec ctxToAVarSub = function (I.Null, s) -> s | (I.Decl (G, I.Dec (_, A)), s) -> ( let X = I.newEVar (I.Null, A) in  I.Dot (I.Exp (X), ctxToAVarSub (G, s)) ) | (I.Decl (G, I.ADec (_, d)), s) -> ( let X = I.newAVar () in  I.Dot (I.Exp (I.EClo (X, I.Shift (~- d))), ctxToAVarSub (G, s)) )
(* ---------------------------------------------------------------------- *)

(* Solving  variable definitions *)

(* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G  . |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)

let rec solveEqn = function ((T.Trivial, s), G) -> true | ((T.Unify (G', e1, N, eqns), s), G) -> ( (* G, G' |- s' : D, G, G' *)
let G'' = append (G', G) in let s' = shift (G'', s) in  Assign.unifiable (G'', (N, s'), (e1, s')) && solveEqn ((eqns, s), G) )
let rec unifySub' (G, s1, s2)  = try (Unify.unifySub (G, s1, s2); true) with Unify.Unify msg -> false
let rec unify (G, Us, Us')  = try (Unify.unify (G, Us, Us'); true) with Unify.Unify msg -> false
let rec getHypGoal = function (DProg, (C.Atom p, s)) -> (DProg, (p, s)) | (C.DProg (G, dPool), (C.Impl (r, A, Ha, g), s)) -> ( let D' = IntSyn.Dec (None, I.EClo (A, s)) in  if (! TableParam.strengthen) then (match MT.memberCtx ((G, I.EClo (A, s)), G) with Some (_) -> (( (* is g always atomic? *)
let C.Atom (p) = g in let X = I.newEVar (G, I.EClo (A, s)) in  getHypGoal (C.DProg (G, dPool), (g, I.Dot (I.Exp (X), s))) )) | None -> getHypGoal (C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))), (g, I.dot1 s))) else getHypGoal (C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))), (g, I.dot1 s)) ) | (C.DProg (G, dPool), (C.All (D, g), s)) -> ( let D' = I.decSub (D, s) in  getHypGoal (C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)), (g, I.dot1 s)) )
let rec updateGlobalTable (goal, flag)  = ( let (dProg, (p, s)) = getHypGoal (C.DProg (I.Null, I.Null), (goal, I.id)) in let (G', DAVars, DEVars, U', eqn', s') = A.abstractEVarCtx (dProg, p, s) in let _ = if solveEqn ((eqn', s'), G') then () else print "\nresidual equation not solvable!\n" in let status = if flag then TableParam.Complete else TableParam.Incomplete in  if TabledSyn.keepTable (IntSyn.targetFam U') then match MT.callCheck (DAVars, DEVars, G', U', eqn', status) with T.RepeatedEntry (_, answRef, _) -> (TableParam.globalTable := ((DAVars, DEVars, G', U', eqn', answRef, status) :: (! TableParam.globalTable))) | _ -> raise (Error "Top level goal should always in the table\n") else () )
let rec keepTable c  = TabledSyn.keepTable c
let rec fillTable ()  = ( let rec insert = function ([]) -> () | ((DAVars, DEVars, G', U', eqn', answRef, status) :: T) -> match MT.insertIntoTree (DAVars, DEVars, G', U', eqn', answRef, status) with T.NewEntry (_) -> insert T | _ -> () in  insert (! TableParam.globalTable) )
(*------------------------------------------------------------------------------------------*)

(* retrieve' ((G, U, s), asub, AnswerList, sc) = ()

     retrieval for_sml subsumption must take into account the asub substitution

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

let rec retrieve' = function ((G, U, s), asub, [], sc) -> () | ((G, U, s), (esub, asub), (((D', s1), O1) :: A), sc) -> ( let s1' = ctxToEVarSub (D', I.Shift (I.ctxLength (D'))(* I.id *)
) in let scomp = I.comp (s1, s1') in let ss = shift (G, s) in let ss1 = shift (G, scomp) in let a = I.comp (asub, s) in let ass = shift (G, a) in let easub = I.comp (asub, esub) in  Cs.CSManager.trail (fun () -> if (unifySub' (G, shift (G, esub), ss) && unifySub' (G, shift (G, I.comp (asub, esub)), ss1)) then (sc O1)(* Succeed *)
 else ()); (* Fail *)
retrieve' ((G, U, s), (esub, asub), A, sc) )
(* currently not used -- however, it may be better to not use the same retrieval function for_sml
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

let rec retrieveV = function ((G, U, s), [], sc) -> () | ((G, U, s), (((DEVars, s1), O1) :: A), sc) -> ( (* for_sml subsumption we must combine it with asumb!!! *)
let s1' = ctxToEVarSub (DEVars, I.Shift (I.ctxLength (DEVars))(* I.id *)
) in let scomp = I.comp (s1, s1') in let ss = shift (G, s) in let ss1 = shift (G, scomp) in  Cs.CSManager.trail (fun () -> if unifySub' (G, ss, ss1) then (sc O1) else ()); retrieveV ((G, U, s), A, sc) )
let rec retrieveSW ((G, U, s), asub, AnswL, sc)  = retrieve' ((G, U, s), asub, AnswL, sc)
(* currently not used -- however, it may be better to  not use the same retrieval function for_sml
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

let rec retrieve (k, (G, U, s), (asub, answRef), sc)  = ( let lkp = T.lookup (answRef) in let asw' = List.take (rev (T.solutions (answRef)), T.lookup (answRef)) in let answ' = List.drop (asw', ! k) in  k := lkp; retrieveSW ((G, U, s), asub, answ', sc) )
(* ---------------------------------------------------------------------- *)

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

let rec solve = function ((C.Atom (p), s), dp, sc) -> if TabledSyn.tabledLookup (I.targetFam p) then ( (* Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *)
let (G', DAVars, DEVars, U', eqn', s') = A.abstractEVarCtx (dp, p, s) in let _ = if solveEqn ((eqn', s'), G') then () else print "\nresidual equation not solvable! -- This should never happen! \n" in  match MT.callCheck (DAVars, DEVars, G', U', eqn', T.Incomplete)(* Side effect: D', G' |- U' added to table *)
 with T.NewEntry (answRef) -> matchAtom ((p, s), dp, (fun pskeleton -> match MT.answerCheck (s', answRef, pskeleton) with T.Repeated -> () | T.New_ -> (sc pskeleton))) | T.RepeatedEntry (asub, answRef, T.Incomplete) -> if T.noAnswers answRef then (* loop detected
                  * NOTE: we might suspend goals more than once.
                  *     example: answer list for_sml goal (p,s) is saturated
                  *              but not the whole table is saturated.
                  *)
(SuspGoals := ((Loop, (G', U', s'), sc, Unify.suspend (), (asub, answRef), ref 0) :: (! SuspGoals)); ()) else (* loop detected
                  * new answers available from previous stages
                  * resolve current goal with all possible answers
                  *)
( let le = T.lookup (answRef) in  SuspGoals := ((Loop, (G', U', s'), sc, Unify.suspend (), (asub, answRef), ref le) :: (! SuspGoals)); retrieve (ref 0, (G', U', s'), (asub, answRef), sc) ) | T.RepeatedEntry (asub, answRef, T.Complete) -> if T.noAnswers answRef then (* Subgoal is not provable *)
() else (* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *)
retrieve (ref 0, (G', U', s'), (asub, answRef), sc) | T.DivergingEntry (asub, answRef) -> (* loop detected  -- currently not functioning correctly.
                    we might be using part of a debugger which suggests diverging goals
                    to the user so the user can prove a generalized goal first.
                    Wed Dec 22 08:27:24 2004 -bp
                  *)
(SuspGoals := ((Divergence ((p, s), dp), (G', U', s'), sc, Unify.suspend (), ((I.id(* this is a hack *)
, asub), answRef), ref 0) :: (! SuspGoals)); ()) ) else matchAtom ((p, s), dp, sc) | ((C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc) -> ( let D' = I.Dec (None, I.EClo (A, s)) in  if (! TableParam.strengthen) then (match MT.memberCtx ((G, I.EClo (A, s)), G) with Some (_) -> (( let X = I.newEVar (G, I.EClo (A, s)) in  solve ((g, I.Dot (I.Exp (X), s)), C.DProg (G, dPool), (fun O -> sc O)) )) | None -> solve ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))), (fun O -> sc O))) else solve ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Dec (r, s, Ha))), (fun O -> sc O)) ) | ((C.All (D, g), s), C.DProg (G, dPool), sc) -> ( let D' = I.decSub (D, s) in  solve ((g, I.dot1 s), C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)), (fun O -> sc O)) )
and rSolve = function (ps', (C.Eq (Q), s), C.DProg (G, dPool), sc) -> (if Unify.unifiable (G, ps', (Q, s))(* effect: instantiate EVars *)
 then sc [](* call success continuation *)
 else ()) | (ps', (C.Assign (Q, eqns), s), dp, sc) -> (match Assign.assignable (G, ps', (Q, s)) with Some (cnstr) -> aSolve ((eqns, s), dp, cnstr, (fun S -> sc S)) | None -> ()) | (ps', (C.And (r, A, g), s), dp, sc) -> ( (* is this EVar redundant? -fp *)
let X = I.newEVar (G, I.EClo (A, s)) in  rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp, (fun S1 -> solve ((g, s), dp, (fun S2 -> sc (S1 @ S2))))) ) | (ps', (C.Exists (I.Dec (_, A), r), s), dp, sc) -> ( let X = I.newEVar (G, I.EClo (A, s)) in  rSolve (ps', (r, I.Dot (I.Exp (X), s)), dp, (fun S -> sc S)) ) | (ps', (C.Axists (I.ADec (Some (X), d), r), s), dp, sc) -> ( let X' = I.newAVar () in  rSolve (ps', (r, I.Dot (I.Exp (I.EClo (X', I.Shift (~- d))), s)), dp, sc)(* we don't increase the proof term here! *)
 )
and aSolve = function ((C.Trivial, s), dp, cnstr, sc) -> (if Assign.solveCnstr cnstr then (sc []) else ()) | ((C.UnifyEq (G', e1, N, eqns), s), dp, cnstr, sc) -> ( let (G'') = append (G', G) in let s' = shift (G', s) in  if Assign.unifiable (G'', (N, s'), (e1, s')) then aSolve ((eqns, s), dp, cnstr, sc) else () )
and matchAtom (ps', dp, sc)  = ( (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for_sml solving atomic goal ps', starting
           with c1.
        *)
(* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for_sml solving atomic goal ps', starting
           with the most recent one.
        *)
let rec matchSig = function [] -> () | ((Hc) :: sgn') -> ( let C.SClause (r) = C.sProgLookup (cidFromHead Hc) in  (* trail to undo EVar instantiations *)
Cs.CSManager.trail (fun () -> rSolve (ps', (r, I.id), dp, (fun S -> sc ((C.Pc c) :: S)))); matchSig sgn' ) in let rec matchDProg = function (I.Null, I.Null, _) -> matchSig (Index.lookup (cidFromHead Ha)) | (I.Decl (G, _), I.Decl (dPool', C.Dec (r, s, Ha')), k) -> if eqHead (Ha, Ha') then (* trail to undo EVar instantiations *)
(Cs.CSManager.trail (fun () -> rSolve (ps', (r, I.comp (s, I.Shift (k))), dp, (fun S -> sc ((C.Dc k) :: S)))); matchDProg (G, dPool', k + 1)) else matchDProg (G, dPool', k + 1) | (I.Decl (G, _), I.Decl (dPool', C.Parameter), k) -> matchDProg (G, dPool', k + 1) in let rec matchConstraint (solve, try_)  = ( let succeeded = Cs.CSManager.trail (fun () -> match (solve (G, I.SClo (S, s), try_)) with Some (U) -> (sc [C.Csolver U]; true) | None -> false) in  if succeeded then matchConstraint (solve, try_ + 1) else () ) in  match I.constStatus (cidFromHead Ha) with (I.Constraint (cs, solve)) -> matchConstraint (solve, 0) | _ -> matchDProg (G, dPool, 1) )
(* retrieval ((p, s), dp, sc, answRef, n) => ()
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

let rec retrieval = function (Loop, (G', U', s'), sc, (asub, answRef), n) -> if T.noAnswers answRef then (* still  no answers available from previous stages *)
(* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
() else (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *)
retrieve (n, (G', U', s'), (asub, answRef), sc) | (Divergence ((p, s), dp), (G', U', s'), sc, (asub, answRef), n) -> matchAtom ((p, s), dp, (fun pskeleton -> match MT.answerCheck (s', answRef, pskeleton) with T.Repeated -> () | T.New_ -> sc pskeleton))
let rec tableSize ()  = MT.tableSize ()
let rec suspGoalNo ()  = List.length (! SuspGoals)
(*  nextStage () = bool
     Side effect: advances lookup pointers
   *)

let rec nextStage ()  = ( let rec resume = function [] -> () | (((Susp, s, sc, trail, (asub, answRef), k) :: Goals)) -> (Cs.CSManager.trail (fun () -> (Unify.resume trail; retrieval (Susp, s, sc, (asub, answRef), k))); resume (Goals)) in let SG = rev (! SuspGoals) in  if MT.updateTable () then (* table changed during previous stage *)
(TableParam.stageCtr := (! TableParam.stageCtr) + 1; resume (SG); true) else (* table did not change during previous stage *)
false )
let rec reset ()  = (SuspGoals := []; MT.reset (); TableParam.stageCtr := 0)
let rec solveQuery ((g, s), dp, sc)  = (* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)
 solve ((g, s), dp, sc)
(* local ... *)

let solve = solveQuery
 end


(* functor Tabled *)

