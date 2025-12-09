(* Strategy *)
(* Author: Carsten Schuermann *)

module StrategyFRS (MetaGlobal : METAGLOBAL)
   (module MetaSyn' : METASYN)
   (Filling : FILLING)
                     sharing Filling.MetaSyn = MetaSyn'
                     (Splitting : SPLITTING)
                     sharing Splitting.MetaSyn = MetaSyn'
                     (Recursion : RECURSION)
                     sharing Recursion.MetaSyn = MetaSyn'
                     (Lemma : LEMMA)
                     sharing Lemma.MetaSyn = MetaSyn'
                     (Qed : QED)
                     sharing Qed.MetaSyn = MetaSyn'
                     (MetaPrint : METAPRINT)
                     sharing MetaPrint.MetaSyn = MetaSyn'
                     (Timers : TIMERS)
  : STRATEGY =
struct

  module MetaSyn = MetaSyn'

  local

    module M = MetaSyn

    let rec printInit () =
        if !Global.chatter > 3 then print "Strategy 1.0: FRS\n"
        else ()

    let rec printFinish (M.State (name, _, _)) =
        if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
        else if !Global.chatter> 4 then print ("[" ^ name ^ "]\n")
             else if !Global.chatter> 3 then print ("[" ^ name ^ "]")
                  else ()

    let rec printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    let rec printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    let rec printSplitting () =
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    let rec printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    let rec printQed () =
        if !Global.chatter > 3 then print ("[QED]\n")
        else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    let rec findMin = function nil -> NONE
      | (O :: L) -> 
        let
          let rec findMin' (nil, k, result) = result
            | findMin' (O' :: L', k ,result)=
                let
                  let k' = Splitting.index O'
                in
                  if Splitting.index O' < k then findMin' (L', k', SOME O')
                  else findMin' (L', k, result)
                end
        in
          findMin' (L, Splitting.index O, SOME O)
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
    let rec split (S :: givenStates, os as (openStates, solvedStates)) =
        case findMin ((Timers.time Timers.splitting Splitting.expand) S)
          of NONE => fill (givenStates, (S :: openStates, solvedStates))
           | SOME splitOp =>
             let
               let _ = printSplitting ()
               let SL = (Timers.time Timers.splitting Splitting.apply) splitOp
               let _ = printCloseBracket ()
             in
               (fill (SL @ givenStates, os)
                handle Splitting.Error _ => fill (givenStates, (S :: openStates, solvedStates)))
             end

    and recurse (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion Recursion.expandEager) S
          of nil => split (S :: givenStates, os)
           | (recursionOp :: _) =>
             let
               let _ = printRecursion ()
               let S' = (Timers.time Timers.recursion Recursion.apply) recursionOp
               let _ = printCloseBracket ()
             in
               (fill (S' :: givenStates, (openStates, solvedStates))
                handle Recursion.Error _ => split (S :: givenStates, os))
             end

    and fill (nil, os) = os
      | fill (S :: givenStates, os as (openStates, solvedStates)) =
      let
        let rec fillOp () =
          case (Timers.time Timers.filling Filling.expand) S
            of (_, fillingOp) =>
              (let
                 let _ = printFilling ()
                 let [S'] = (Timers.time Timers.filling Filling.apply) fillingOp
                 let _ = printCloseBracket ()
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

      end

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    let rec run givenStates =
        let
          let _ = printInit ()
          let os = fill (givenStates, (nil, nil))
          let _ = case os
                    of (nil, _) => printQed ()
                     | _ => ()
        in
          os
        end
  in
    let run = run
  end (* local *)
end;; (* functor StrategyFRS *)



module StrategyRFS (MetaGlobal : METAGLOBAL)
   (module MetaSyn' : METASYN)
   (Filling : FILLING)
                     sharing Filling.MetaSyn = MetaSyn'
                     (Splitting : SPLITTING)
                     sharing Splitting.MetaSyn = MetaSyn'
                     (Recursion : RECURSION)
                     sharing Recursion.MetaSyn = MetaSyn'
                     (Lemma : LEMMA)
                     sharing Lemma.MetaSyn = MetaSyn'
                     (Qed : QED)
                     sharing Qed.MetaSyn = MetaSyn'
                     (MetaPrint : METAPRINT)
                     sharing MetaPrint.MetaSyn = MetaSyn'
                     (Timers : TIMERS)
  : STRATEGY =
struct

  module MetaSyn = MetaSyn'

  local

    module M = MetaSyn

    let rec printInit () =
        if !Global.chatter > 3 then print "Strategy 1.0: RFS\n"
        else ()

    let rec printFinish (M.State (name, _, _)) =
        if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
        else if !Global.chatter> 4 then print ("[" ^ name ^ "]\n")
             else if !Global.chatter> 3 then print ("[" ^ name ^ "]")
                  else ()

    let rec printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    let rec printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    let rec printSplitting () =
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    let rec printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    let rec printQed () =
        if !Global.chatter > 3 then print ("[QED]\n")
        else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    let rec findMin = function nil -> NONE
      | (O :: L) -> 
          let
            let rec findMin' (nil, k, result) = result
              | findMin' (O' :: L', k ,result)=
                  let
                    let k' = Splitting.index O'
                  in
                    if Splitting.index O' < k then findMin' (L', k', SOME O')
                    else findMin' (L', k, result)
                  end
          in
            findMin' (L, Splitting.index O, SOME O)
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
    let rec split (S :: givenStates, os as (openStates, solvedStates)) =
        case findMin ((Timers.time Timers.splitting Splitting.expand) S) of
          NONE => recurse (givenStates, (S :: openStates, solvedStates))
        | SOME splitOp =>
            let
              let _ = printSplitting ()
              let SL = (Timers.time Timers.splitting Splitting.apply) splitOp
              let _ = printCloseBracket ()
            in
              (recurse (SL @ givenStates, os)
               handle Splitting.Error _ => recurse (givenStates, (S :: openStates, solvedStates)))
            end

    and fill (nil, os) = os
      | fill (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.filling Filling.expand) S
          of (_, fillingOp) =>
             (let
                let _ = printFilling ()
                let [S'] = (Timers.time Timers.filling Filling.apply) fillingOp
                let _ = printCloseBracket ()
              in
                if Qed.subgoal S' then
                  (printFinish S'; recurse (givenStates, (openStates, S' :: solvedStates)))
                else fill (S' :: givenStates, os)
              end
                handle Filling.Error _ => split (S :: givenStates, os))

    and recurse (nil, os) = os
      | recurse (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion Recursion.expandEager) S
          of nil => fill (S :: givenStates, os)
           | (recursionOp :: _) =>
             let
               let _ = printRecursion ()
               let S' = (Timers.time Timers.recursion Recursion.apply) recursionOp
               let _ = printCloseBracket ()
             in
               (recurse (S' :: givenStates, (openStates, solvedStates))
                handle Recursion.Error _ => fill (S :: givenStates, os))
             end

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    let rec run givenStates =
        let
          let _ = printInit ()
          let os = recurse (givenStates, (nil, nil))
          let _ = case os
                    of (nil, _) => printQed ()
                     | _ => ()
        in
          os
        end
  in
    let run = run
  end (* local *)
end;; (* functor StrategyRFS *)



module Strategy (MetaGlobal : METAGLOBAL)
   (module MetaSyn' : METASYN)
   (StrategyFRS : STRATEGY)
                  sharing StrategyFRS.MetaSyn = MetaSyn'
                  (StrategyRFS : STRATEGY)
                  sharing StrategyRFS.MetaSyn = MetaSyn')
  : STRATEGY =
struct

  module MetaSyn = MetaSyn'

  let rec run SL =
      case !MetaGlobal.strategy
        of MetaGlobal.RFS => StrategyRFS.run SL
         | MetaGlobal.FRS => StrategyFRS.run SL

end;; (* functor Strategy *)
