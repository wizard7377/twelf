(* Strategy *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) StrategyFRS (structure MetaGlobal : METAGLOBAL
                     structure MetaSyn' : METASYN
                     structure Filling : FILLING
                     sharing Filling.MetaSyn = MetaSyn'
                     structure Splitting : SPLITTING
                     sharing Splitting.MetaSyn = MetaSyn'
                     structure Recursion : RECURSION
                     sharing Recursion.MetaSyn = MetaSyn'
                     structure Lemma : LEMMA
                     sharing Lemma.MetaSyn = MetaSyn'
                     structure Qed : QED
                     sharing Qed.MetaSyn = MetaSyn'
                     structure MetaPrint : METAPRINT
                     sharing MetaPrint.MetaSyn = MetaSyn'
                     structure Timers : TIMERS)
  : STRATEGY =
struct

  structure MetaSyn = MetaSyn'

  local

    structure M = MetaSyn

    fun printInit () =
        if !Global.chatter > 3 then print "Strategy 1.0: FRS\n"
        else ()

    fun printFinish (M.State (name, _, _)) =
        if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
        else if !Global.chatter> 4 then print ("[" ^ name ^ "]\n")
             else if !Global.chatter> 3 then print ("[" ^ name ^ "]")
                  else ()

    fun printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    fun printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    fun printSplitting () =
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    fun printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    fun printQed () =
        if !Global.chatter > 3 then print ("[QED]\n")
        else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    fun (* GEN BEGIN FUN FIRST *) findMin nil = NONE (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findMin (O :: L) =
        let
          fun (* GEN BEGIN FUN FIRST *) findMin' (nil, k, result) = result (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) findMin' (O' :: L', k ,result)=
                let
                  (* GEN BEGIN TAG OUTSIDE LET *) val k' = Splitting.index O' (* GEN END TAG OUTSIDE LET *)
                in
                  if Splitting.index O' < k then findMin' (L', k', SOME O')
                  else findMin' (L', k, result)
                end (* GEN END FUN BRANCH *)
        in
          findMin' (L, Splitting.index O, SOME O)
        end (* GEN END FUN BRANCH *)

    (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
    fun split (S :: givenStates, os as (openStates, solvedStates)) =
        case findMin ((Timers.time Timers.splitting Splitting.expand) S)
          of NONE => fill (givenStates, (S :: openStates, solvedStates))
           | SOME splitOp =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printSplitting () (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val SL = (Timers.time Timers.splitting Splitting.apply) splitOp (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
             in
               (fill (SL @ givenStates, os)
                handle Splitting.Error _ => fill (givenStates, (S :: openStates, solvedStates)))
             end

    and recurse (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion Recursion.expandEager) S
          of nil => split (S :: givenStates, os)
           | (recursionOp :: _) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printRecursion () (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.recursion Recursion.apply) recursionOp (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
             in
               (fill (S' :: givenStates, (openStates, solvedStates))
                handle Recursion.Error _ => split (S :: givenStates, os))
             end

    and (* GEN BEGIN FUN FIRST *) fill (nil, os) = os (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fill (S :: givenStates, os as (openStates, solvedStates)) =
      let
        fun fillOp () =
          case (Timers.time Timers.filling Filling.expand) S
            of (_, fillingOp) =>
              (let
                 (* GEN BEGIN TAG OUTSIDE LET *) val _ = printFilling () (* GEN END TAG OUTSIDE LET *)
                 (* GEN BEGIN TAG OUTSIDE LET *) val [S'] = (Timers.time Timers.filling Filling.apply) fillingOp (* GEN END TAG OUTSIDE LET *)
                 (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
               in
                 if Qed.subgoal S'
                   then (printFinish S'; fill (givenStates, (openStates, S' :: solvedStates)))
                 else fill (S' :: givenStates, os)
               end
                 handle Filling.Error _ => recurse (S :: givenStates, os))
      in
        (TimeLimit.timeLimit (!Global.timeLimit) fillOp ())
        handle TimeLimit.TimeOut =>
          (print "\n----------- TIME OUT ---------------\n" ; raise Filling.TimeOut)
      
      end (* GEN END FUN BRANCH *)

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    fun run givenStates =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = printInit () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val os = fill (givenStates, (nil, nil)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = case os
                    of (nil, _) => printQed ()
                     | _ => () (* GEN END TAG OUTSIDE LET *)
        in
          os
        end
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val run = run (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *);  (* functor StrategyFRS *)



functor (* GEN BEGIN FUNCTOR DECL *) StrategyRFS (structure MetaGlobal : METAGLOBAL
                     structure MetaSyn' : METASYN
                     structure Filling : FILLING
                     sharing Filling.MetaSyn = MetaSyn'
                     structure Splitting : SPLITTING
                     sharing Splitting.MetaSyn = MetaSyn'
                     structure Recursion : RECURSION
                     sharing Recursion.MetaSyn = MetaSyn'
                     structure Lemma : LEMMA
                     sharing Lemma.MetaSyn = MetaSyn'
                     structure Qed : QED
                     sharing Qed.MetaSyn = MetaSyn'
                     structure MetaPrint : METAPRINT
                     sharing MetaPrint.MetaSyn = MetaSyn'
                     structure Timers : TIMERS)
  : STRATEGY =
struct

  structure MetaSyn = MetaSyn'

  local

    structure M = MetaSyn

    fun printInit () =
        if !Global.chatter > 3 then print "Strategy 1.0: RFS\n"
        else ()

    fun printFinish (M.State (name, _, _)) =
        if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
        else if !Global.chatter> 4 then print ("[" ^ name ^ "]\n")
             else if !Global.chatter> 3 then print ("[" ^ name ^ "]")
                  else ()

    fun printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    fun printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    fun printSplitting () =
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    fun printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    fun printQed () =
        if !Global.chatter > 3 then print ("[QED]\n")
        else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    fun (* GEN BEGIN FUN FIRST *) findMin nil = NONE (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findMin (O :: L) =
          let
            fun (* GEN BEGIN FUN FIRST *) findMin' (nil, k, result) = result (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) findMin' (O' :: L', k ,result)=
                  let
                    (* GEN BEGIN TAG OUTSIDE LET *) val k' = Splitting.index O' (* GEN END TAG OUTSIDE LET *)
                  in
                    if Splitting.index O' < k then findMin' (L', k', SOME O')
                    else findMin' (L', k, result)
                  end (* GEN END FUN BRANCH *)
          in
            findMin' (L, Splitting.index O, SOME O)
          end (* GEN END FUN BRANCH *)

    (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
    fun split (S :: givenStates, os as (openStates, solvedStates)) =
        case findMin ((Timers.time Timers.splitting Splitting.expand) S) of
          NONE => recurse (givenStates, (S :: openStates, solvedStates))
        | SOME splitOp =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = printSplitting () (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val SL = (Timers.time Timers.splitting Splitting.apply) splitOp (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
            in
              (recurse (SL @ givenStates, os)
               handle Splitting.Error _ => recurse (givenStates, (S :: openStates, solvedStates)))
            end

    and (* GEN BEGIN FUN FIRST *) fill (nil, os) = os (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fill (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.filling Filling.expand) S
          of (_, fillingOp) =>
             (let
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = printFilling () (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val [S'] = (Timers.time Timers.filling Filling.apply) fillingOp (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
              in
                if Qed.subgoal S' then
                  (printFinish S'; recurse (givenStates, (openStates, S' :: solvedStates)))
                else fill (S' :: givenStates, os)
              end
                handle Filling.Error _ => split (S :: givenStates, os)) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) recurse (nil, os) = os (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) recurse (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion Recursion.expandEager) S
          of nil => fill (S :: givenStates, os)
           | (recursionOp :: _) =>
             let
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printRecursion () (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val S' = (Timers.time Timers.recursion Recursion.apply) recursionOp (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
             in
               (recurse (S' :: givenStates, (openStates, solvedStates))
                handle Recursion.Error _ => fill (S :: givenStates, os))
             end (* GEN END FUN BRANCH *)

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    fun run givenStates =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = printInit () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val os = recurse (givenStates, (nil, nil)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = case os
                    of (nil, _) => printQed ()
                     | _ => () (* GEN END TAG OUTSIDE LET *)
        in
          os
        end
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val run = run (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *);  (* functor StrategyRFS *)



functor (* GEN BEGIN FUNCTOR DECL *) Strategy (structure MetaGlobal : METAGLOBAL
                  structure MetaSyn' : METASYN
                  structure StrategyFRS : STRATEGY
                  sharing StrategyFRS.MetaSyn = MetaSyn'
                  structure StrategyRFS : STRATEGY
                  sharing StrategyRFS.MetaSyn = MetaSyn')
  : STRATEGY =
struct

  structure MetaSyn = MetaSyn'

  fun run SL =
      case !MetaGlobal.strategy
        of MetaGlobal.RFS => StrategyRFS.run SL
         | MetaGlobal.FRS => StrategyFRS.run SL

end (* GEN END FUNCTOR DECL *); (* functor Strategy *)
