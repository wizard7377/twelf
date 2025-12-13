(* MTP Strategy: Version 1.3 *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) MTPStrategy (structure MTPGlobal : MTPGLOBAL
                     structure StateSyn' : STATESYN
                     structure MTPFilling : MTPFILLING
                       sharing MTPFilling.StateSyn = StateSyn'
                     structure MTPData : MTPDATA
                     structure MTPSplitting : MTPSPLITTING
                       sharing MTPSplitting.StateSyn = StateSyn'
                     structure MTPRecursion : MTPRECURSION
                       sharing MTPRecursion.StateSyn = StateSyn'
                     structure Inference : INFERENCE
                       sharing Inference.StateSyn = StateSyn'
                     structure MTPrint : MTPRINT
                       sharing MTPrint.StateSyn = StateSyn'
                     structure Timers : TIMERS)
  : MTPSTRATEGY =
struct

  structure StateSyn = StateSyn'

  local

    structure S = StateSyn

    fun printInit () =
        if !Global.chatter > 3 then print "Strategy\n"
        else ()

    fun printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    fun printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    fun printInference () =
        if !Global.chatter > 5 then print ("[Inference ...")
        else if !Global.chatter> 4 then print ("I")
             else ()

    fun printSplitting splitOp =
        (* if !Global.chatter > 5 then print ("[" ^ MTPSplitting.menu splitOp) *)
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    fun printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    fun printQed () =
        (if !Global.chatter > 3 then print ("[QED]\n")
         else ();
         if !Global.chatter > 4 then print ("Statistics: required Twelf.Prover.maxFill := "
                                            ^ (Int.toString (!MTPData.maxFill)) ^ "\n")
         else ())

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    fun (* GEN BEGIN FUN FIRST *) findMin nil = NONE (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findMin L =
          let
            fun (* GEN BEGIN FUN FIRST *) findMin' (nil, result) = result (* GEN END FUN FIRST *)
              | (* GEN BEGIN FUN BRANCH *) findMin' (O' :: L', NONE) =
                if MTPSplitting.applicable O' then
                   findMin' (L', SOME O')
                else findMin' (L', NONE) (* GEN END FUN BRANCH *)
              | (* GEN BEGIN FUN BRANCH *) findMin' (O' :: L', SOME O) =
                if MTPSplitting.applicable O' then
                  case MTPSplitting.compare (O', O)
                    of LESS =>  findMin' (L', SOME O')
                     | _ => findMin' (L', SOME O)
                else findMin' (L', SOME O) (* GEN END FUN BRANCH *)
      
          in
            findMin' (L, NONE)
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
        case findMin ((Timers.time Timers.splitting MTPSplitting.expand) S) of
          NONE => fill (givenStates, (S :: openStates, solvedStates))
        | SOME splitOp =>
            let
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = printSplitting splitOp (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val SL = (Timers.time Timers.splitting MTPSplitting.apply) splitOp (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = printRecursion () (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val SL' = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => (Timers.time Timers.recursion MTPRecursion.apply) (MTPRecursion.expand S) (* GEN END FUNCTION EXPRESSION *)) SL (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val _ = printInference () (* GEN END TAG OUTSIDE LET *)
              (* GEN BEGIN TAG OUTSIDE LET *) val SL'' = map ((* GEN BEGIN FUNCTION EXPRESSION *) fn S => (Timers.time Timers.inference Inference.apply) (Inference.expand S) (* GEN END FUNCTION EXPRESSION *)) SL' (* GEN END TAG OUTSIDE LET *)
            in
              fill (SL'' @ givenStates, os)
            end

    and (* GEN BEGIN FUN FIRST *) fill (nil, os) = os (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) fill (S :: givenStates, os as (openStates, solvedStates)) =
        (case (Timers.time Timers.recursion MTPFilling.expand) S
          of fillingOp =>
             (let
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printFilling () (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (max, P) = TimeLimit.timeLimit (!Global.timeLimit)
                                     (Timers.time Timers.filling MTPFilling.apply) fillingOp (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val _ = printCloseBracket () (* GEN END TAG OUTSIDE LET *)
              in
                fill (givenStates, os)
              end)  handle MTPFilling.Error _ => split (S :: givenStates, os)) (* GEN END FUN BRANCH *)

           (* Note: calling splitting in case filling fails, may cause the prover to succeed
              if there are no cases to split -- however this may in fact be wrong -bp*)
           (* for comparing depth-first search (logic programming) with iterative deepening search
              in the meta-theorem prover, we must disallow splitting :

                handle TimeLimit.TimeOut =>  raise Filling.Error "Time Out: Time limit exceeded\n"
                handle MTPFilling.Error msg =>  raise Filling.Error msg
                  ) handle MTPFilling.Error msg =>  raise Filling.Error msg
            *)

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    fun run givenStates =
        (let
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = printInit () (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (openStates, solvedStates) = fill (givenStates, (nil, nil)) (* GEN END TAG OUTSIDE LET *)
    
          (* GEN BEGIN TAG OUTSIDE LET *) val openStates' = map MTPrint.nameState openStates (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val solvedStates' = map MTPrint.nameState solvedStates (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val _ = case openStates
                    of nil => printQed ()
                     | _ => () (* GEN END TAG OUTSIDE LET *)
        in
          (openStates', solvedStates')
        end)


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val run = run (* GEN END TAG OUTSIDE LET *)
  end (* local *)
end (* GEN END FUNCTOR DECL *);  (* functor StrategyFRS *)


