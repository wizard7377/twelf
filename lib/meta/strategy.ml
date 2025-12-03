(* MTP Strategy: Version 1.3 *)
(* Author: Carsten Schuermann *)

let recctor MTPStrategy (module MTPGlobal : MTPGLOBAL
                     module StateSyn' : STATESYN
                     module MTPFilling : MTPFILLING
                       sharing MTPFilling.StateSyn = StateSyn'
                     module MTPData : MTPDATA
                     module MTPSplitting : MTPSPLITTING
                       sharing MTPSplitting.StateSyn = StateSyn'
                     module MTPRecursion : MTPRECURSION
                       sharing MTPRecursion.StateSyn = StateSyn'
                     module Inference : INFERENCE
                       sharing Inference.StateSyn = StateSyn'
                     module MTPrint : MTPRINT
                       sharing MTPrint.StateSyn = StateSyn'
                     module Timers : TIMERS)
  : MTPSTRATEGY =
struct

  module StateSyn = StateSyn'

  local

    module S = StateSyn

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
    fun findMin nil = NONE
      | findMin L =
          let
            fun findMin' (nil, result) = result
              | findMin' (O' :: L', NONE) =
                if MTPSplitting.applicable O' then
                   findMin' (L', SOME O')
                else findMin' (L', NONE)
              | findMin' (O' :: L', SOME O) =
                if MTPSplitting.applicable O' then
                  case MTPSplitting.compare (O', O)
                    of LESS =>  findMin' (L', SOME O')
                     | _ => findMin' (L', SOME O)
                else findMin' (L', SOME O)

          in
            findMin' (L, NONE)
          end

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
              let _ = printSplitting splitOp
              let SL = (Timers.time Timers.splitting MTPSplitting.apply) splitOp
              let _ = printCloseBracket ()
              let _ = printRecursion ()
              let SL' = map (fun S -> (Timers.time Timers.recursion MTPRecursion.apply) (MTPRecursion.expand S)) SL
              let _ = printInference ()
              let SL'' = map (fun S -> (Timers.time Timers.inference Inference.apply) (Inference.expand S)) SL'
            in
              fill (SL'' @ givenStates, os)
            end

    and fill (nil, os) = os
      | fill (S :: givenStates, os as (openStates, solvedStates)) =
        (case (Timers.time Timers.recursion MTPFilling.expand) S
          of fillingOp =>
             (let
               let _ = printFilling ()
               let (max, P) = TimeLimit.timeLimit (!Global.timeLimit)
                                     (Timers.time Timers.filling MTPFilling.apply) fillingOp
               let _ = printCloseBracket ()
              in
                fill (givenStates, os)
              end)  handle MTPFilling.Error _ => split (S :: givenStates, os))

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
          let _ = printInit ()
          let (openStates, solvedStates) = fill (givenStates, (nil, nil))

          let openStates' = map MTPrint.nameState openStates
          let solvedStates' = map MTPrint.nameState solvedStates
          let _ = case openStates
                    of nil => printQed ()
                     | _ => ()
        in
          (openStates', solvedStates')
        end)


  in
    let run = run
  end (* local *)
end;  (* functor StrategyFRS *)


