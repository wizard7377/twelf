(* Total Declarations *)
(* Author: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) Total
  (structure Global : GLOBAL
   structure Table : TABLE where type key = int

   (*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)

   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)

   structure ModeTable : MODETABLE
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure ModeCheck : MODECHECK

   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)

   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)

   structure Order : ORDER
   (*! sharing Order.IntSyn = IntSyn' !*)
   structure Reduces : REDUCES
   (*! sharing Reduces.IntSyn = IntSyn' !*)

   structure Cover : COVER

     (*! structure Paths : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths !*)
     (*! sharing Origins.IntSyn = IntSyn' !*)

   structure Timers : TIMERS)
   : TOTAL =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure P = Paths
    structure M = ModeSyn
    structure N = Names

    (* totalTable (a) = SOME() iff a is total, otherwise NONE *)
    (* GEN BEGIN TAG OUTSIDE LET *) val totalTable : unit Table.table = Table.new(0) (* GEN END TAG OUTSIDE LET *)

    fun reset () = Table.clear totalTable
    fun install (cid) = Table.insert totalTable (cid, ())
    fun lookup (cid) = Table.lookup totalTable (cid)
    fun uninstall (cid) = Table.delete totalTable (cid)
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val reset = reset (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val install = install (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val uninstall = ((* GEN BEGIN FUNCTION EXPRESSION *) fn cid =>
        case lookup cid
          of NONE => false
           | SOME _ => (uninstall cid ; true) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    fun total (cid) = (* call only on constants *)
        case lookup cid
          of NONE => false
           | SOME _ => true

    exception Error' of P.occ * string

    (* copied from terminates/reduces.fun *)
    fun error (c, occ, msg) =
        (case Origins.originLookup c
           of (fileName, NONE) => raise Error (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) =>
                raise Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                                        Origins.linesInfoLookup (fileName),
                                        msg)))

    (* G is unused here *)
    fun (* GEN BEGIN FUN FIRST *) checkDynOrder (G, Vs, 0, occ) =
        (* raise Error' (occ, "Output coverage for clauses of order >= 3 not yet implemented") *)
        (* Functional calculus now checks this *)
        (* Sun Jan  5 12:17:06 2003 -fp *)
        (if !Global.chatter >= 5
           then print ("Output coverage: skipping redundant checking of third-order clause\n")
         else ();
         ()) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkDynOrder (G, Vs, n, occ) = (* n > 0 *)
          checkDynOrderW (G, Whnf.whnf Vs, n, occ) (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) checkDynOrderW (G, (I.Root _, s), n, occ) = () (* GEN END FUN FIRST *)
        (* atomic subgoal *)
      | (* GEN BEGIN FUN BRANCH *) checkDynOrderW (G, (I.Pi ((D1 as I.Dec (_, V1), I.No), V2), s), n, occ) =
        (* dynamic (= non-dependent) assumption --- calculate dynamic order of V1 *)
          ( checkDynOrder (G, (V1, s), n-1, P.label occ) ;
            checkDynOrder (I.Decl (G, D1), (V2, I.dot1 s), n, P.body occ) ) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkDynOrderW (G, (I.Pi ((D1, I.Maybe), V2), s), n, occ) =
        (* static (= dependent) assumption --- consider only body *)
          checkDynOrder (I.Decl (G, D1), (V2, I.dot1 s), n, P.body occ) (* GEN END FUN BRANCH *)

    (* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for V is satisfied
           for clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: G |- V[s] : type
    *)
    fun checkClause (G, Vs, occ) = checkClauseW (G, Whnf.whnf Vs, occ)
    and (* GEN BEGIN FUN FIRST *) checkClauseW (G, (I.Pi ((D1, I.Maybe), V2), s), occ) =
        (* quantifier *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val D1' = N.decEName (G, I.decSub (D1, s)) (* GEN END TAG OUTSIDE LET *)
        in
          checkClause (I.Decl (G, D1'), (V2, I.dot1 s), P.body occ)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkClauseW (G, (I.Pi ((D1 as I.Dec (_, V1), I.No), V2), s), occ) =
        (* subgoal *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkClause (I.Decl (G, D1), (V2, I.dot1 s), P.body occ) (* GEN END TAG OUTSIDE LET *)
        in
          checkGoal (G, (V1, s), P.label occ)
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkClauseW (G, (I.Root _, s), occ) =
        (* clause head *)
        () (* GEN END FUN BRANCH *)

    and checkGoal (G, Vs, occ) = checkGoalW (G, Whnf.whnf Vs, occ)
    and checkGoalW (G, (V, s), occ) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val a = I.targetFam V (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if not (total a)
                    then raise Error' (occ, "Subgoal " ^ N.qidToString (N.constQid a)
                                       ^ " not declared to be total")
                  else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkDynOrderW (G, (V, s), 2, occ) (* GEN END TAG OUTSIDE LET *)
                 (* can raise Cover.Error for third-order clauses *)
        in
          Cover.checkOut (G, (V, s))
          handle Cover.Error (msg)
          => raise Error' (occ, "Totality: Output of subgoal not covered\n" ^ msg)
        end

    (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)
    fun (* GEN BEGIN FUN FIRST *) checkDefinite (a, M.Mnil) = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkDefinite (a, M.Mapp (M.Marg (M.Plus, _), ms')) = checkDefinite (a, ms') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkDefinite (a, M.Mapp (M.Marg (M.Minus, _), ms')) = checkDefinite (a, ms') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkDefinite (a, M.Mapp (M.Marg (M.Star, xOpt), ms')) =
        (* Note: filename and location are missing in this error message *)
        (* Fri Apr  5 19:25:54 2002 -fp *)
        error (a, P.top,
               "Error: Totality checking " ^ N.qidToString (N.constQid a) ^ ":\n"
               ^ "All argument modes must be input (+) or output (-)"
               ^ (case xOpt of NONE => ""
                     | SOME(x) => " but argument " ^ x ^ " is indefinite (*)"  )) (* GEN END FUN BRANCH *)

    (* checkOutCover [c1,...,cn] = ()
       iff local output coverage for every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
    fun (* GEN BEGIN FUN FIRST *) checkOutCover nil = () (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) checkOutCover (I.Const(c)::cs) =
        ( if !Global.chatter >= 4
            then print (N.qidToString (N.constQid c) ^ " ")
          else () ;
          if !Global.chatter >= 6
            then print ("\n")
          else () ;
          checkClause (I.Null, (I.constType (c), I.id), P.top)
             handle Error' (occ, msg) => error (c, occ, msg) ;
          checkOutCover cs ) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) checkOutCover (I.Def(d)::cs) =
        ( if !Global.chatter >= 4
            then print (N.qidToString (N.constQid d) ^ " ")
          else () ;
          if !Global.chatter >= 6
            then print ("\n")
          else () ;
          checkClause (I.Null, (I.constType (d), I.id), P.top)
             handle Error' (occ, msg) => error (d, occ, msg) ;
          checkOutCover cs ) (* GEN END FUN BRANCH *)

    (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
    fun checkFam (a) =
        let
          (* Ensuring that there is no bad interaction with type-level definitions *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Cover.checkNoDef (a) (* GEN END TAG OUTSIDE LET *)  (* a cannot be a type-level definition *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = Subordinate.checkNoDef (a) (* a cannot depend on type-level definitions *)
                  handle Subordinate.Error (msg) =>
                            raise Subordinate.Error ("Totality checking " ^
                                                     N.qidToString (N.constQid a)
                                                     ^ ":\n" ^ msg) (* GEN END TAG OUTSIDE LET *)
          (* Checking termination *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = ((Timers.time Timers.terminate Reduces.checkFam) a;
                   if !Global.chatter >= 4
                     then print ("Terminates: " ^ N.qidToString (N.constQid a) ^ "\n")
                   else ())
                  handle Reduces.Error (msg) => raise Reduces.Error (msg) (* GEN END TAG OUTSIDE LET *)
    
          (* Checking input coverage *)
          (* by termination invariant, there must be consistent mode for a *)
          (* GEN BEGIN TAG OUTSIDE LET *) val SOME(ms) = ModeTable.modeLookup a (* GEN END TAG OUTSIDE LET *) (* must be defined and well-moded *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = checkDefinite (a, ms) (* GEN END TAG OUTSIDE LET *) (* all arguments must be either input or output *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = ((Timers.time Timers.coverage Cover.checkCovers) (a, ms) ;
                   if !Global.chatter >= 4
                     then print ("Covers (input): " ^ N.qidToString (N.constQid a) ^ "\n")
                   else ())
                  handle Cover.Error (msg) => raise Cover.Error (msg) (* GEN END TAG OUTSIDE LET *)
    
          (* Checking output coverage *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = if !Global.chatter >= 4
                    then print ("Output coverage checking family " ^ N.qidToString (N.constQid a)
                                ^ "\n")
                  else () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = ModeCheck.checkFreeOut (a, ms) (* GEN END TAG OUTSIDE LET *) (* all variables in output args must be free *)
          (* GEN BEGIN TAG OUTSIDE LET *) val cs = Index.lookup a (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = ((Timers.time Timers.coverage checkOutCover) (cs);
                   if !Global.chatter = 4
                     then print ("\n")
                   else ();
                   if !Global.chatter >= 4
                     then print ("Covers (output): " ^ N.qidToString (N.constQid a) ^ "\n")
                   else ())
                  handle Cover.Error (msg) => raise Cover.Error (msg) (* GEN END TAG OUTSIDE LET *)
        in
          ()
        end
  end

end (* GEN END FUNCTOR DECL *);  (* functor Total *)
