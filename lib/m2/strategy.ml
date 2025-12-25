open Basis ;; 
(* Strategy *)

(* Author: Carsten Schuermann *)

module type STRATEGY = sig
  module MetaSyn : Metasyn.METASYN

  val run : MetaSyn.state list -> MetaSyn.state list * MetaSyn.state list
  (* open cases -> remaining cases * solved cases *)
end

(* signature STRATEGY *)
(* Strategy *)

(* Author: Carsten Schuermann *)

module StrategyFRS
    (MetaGlobal : Meta_global.METAGLOBAL)
    (MetaSyn' : Metasyn.METASYN)
    (Filling : Filling.Fill.FILLING)
    (Splitting : Splitting.Split.SPLITTING)
    (Recursion : Recursion.RECURSION)
    (Lemma : Lemma.LEMMA)
    (Qed : Qed.QED)
    (MetaPrint : Meta_print.METAPRINT)
    (Timers : Timers.TIMERS) : STRATEGY = struct
  module MetaSyn = MetaSyn'
  module M = MetaSyn

  let rec printInit () =
    if !Global.chatter > 3 then print "Strategy 1.0: FRS\n" else ()

  let rec printFinish (M.State (name, _, _)) =
    if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
    else if !Global.chatter > 4 then print ("[" ^ name ^ "]\n")
    else if !Global.chatter > 3 then print ("[" ^ name ^ "]")
    else ()

  let rec printFilling () =
    if !Global.chatter > 5 then print "[Filling ... "
    else if !Global.chatter > 4 then print "F"
    else ()

  let rec printRecursion () =
    if !Global.chatter > 5 then print "[Recursion ..."
    else if !Global.chatter > 4 then print "R"
    else ()

  let rec printSplitting () =
    if !Global.chatter > 5 then print "[Splitting ..."
    else if !Global.chatter > 4 then print "S"
    else ()

  let rec printCloseBracket () = if !Global.chatter > 5 then print "]\n" else ()
  let rec printQed () = if !Global.chatter > 3 then print "[Qed.QED]\n" else ()
  (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)

  let rec findMin = function
    | [] -> None
    | O :: L ->
        let rec findMin' = function
          | [], k, result -> result
          | O' :: L', k, result ->
              let k' = Splitting.index O' in
              if Splitting.index O' < k then findMin' (L', k', Some O')
              else findMin' (L', k, result)
        in
        findMin' (L, Splitting.index O, Some O)
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

  let rec split (S :: givenStates, os) =
    match findMin ((Timers.time Timers.splitting Splitting.expand) S) with
    | None -> fill (givenStates, (S :: openStates, solvedStates))
    | Some splitOp -> (
        let _ = printSplitting () in
        let SL = (Timers.time Timers.splitting Splitting.apply) splitOp in
        let _ = printCloseBracket () in
        try fill (SL @ givenStates, os)
        with Splitting.Error _ ->
          fill (givenStates, (S :: openStates, solvedStates)))

  and recurse (S :: givenStates, os) =
    match (Timers.time Timers.recursion Recursion.expandEager) S with
    | [] -> split (S :: givenStates, os)
    | recursionOp :: _ -> (
        let _ = printRecursion () in
        let S' = (Timers.time Timers.recursion Recursion.apply) recursionOp in
        let _ = printCloseBracket () in
        try fill (S' :: givenStates, (openStates, solvedStates))
        with Recursion.Error _ -> split (S :: givenStates, os))

  and fill = function
    | [], os -> os
    | S :: givenStates, os -> (
        let rec fillOp () =
          match (Timers.time Timers.filling Filling.expand) S with
          | _, fillingOp -> (
              try
                let _ = printFilling () in
                let [ S' ] =
                  (Timers.time Timers.filling Filling.apply) fillingOp
                in
                let _ = printCloseBracket () in
                if Qed.subgoal S' then (
                  printFinish S';
                  fill (givenStates, (openStates, S' :: solvedStates)))
                else fill (S' :: givenStates, os)
              with Filling.Error _ -> recurse (S :: givenStates, os))
        in
        try TimeLimit.timeLimit !Global.timeLimit fillOp ()
        with TimeLimit.TimeOut ->
          print "\n----------- TIME OUT ---------------\n";
          raise Filling.TimeOut)
  (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)

  let rec run givenStates =
    let _ = printInit () in
    let os = fill (givenStates, ([], [])) in
    let _ = match os with [], _ -> printQed () | _ -> () in
    os

  let run = run
  (* local *)
end

(* functor StrategyFRS *)

module StrategyRFS
    (MetaGlobal : Meta_global.METAGLOBAL)
    (MetaSyn' : Metasyn.METASYN)
    (Filling : Filling.Fill.FILLING)
    (Splitting : Splitting.Split.SPLITTING)
    (Recursion : Recursion.RECURSION)
    (Lemma : Lemma.LEMMA)
    (Qed : Qed.QED)
    (MetaPrint : Meta_print.METAPRINT)
    (Timers : Timers.TIMERS) : STRATEGY = struct
  module MetaSyn = MetaSyn'
  module M = MetaSyn

  let rec printInit () =
    if !Global.chatter > 3 then print "Strategy 1.0: RFS\n" else ()

  let rec printFinish (M.State (name, _, _)) =
    if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
    else if !Global.chatter > 4 then print ("[" ^ name ^ "]\n")
    else if !Global.chatter > 3 then print ("[" ^ name ^ "]")
    else ()

  let rec printFilling () =
    if !Global.chatter > 5 then print "[Filling ... "
    else if !Global.chatter > 4 then print "F"
    else ()

  let rec printRecursion () =
    if !Global.chatter > 5 then print "[Recursion ..."
    else if !Global.chatter > 4 then print "R"
    else ()

  let rec printSplitting () =
    if !Global.chatter > 5 then print "[Splitting ..."
    else if !Global.chatter > 4 then print "S"
    else ()

  let rec printCloseBracket () = if !Global.chatter > 5 then print "]\n" else ()
  let rec printQed () = if !Global.chatter > 3 then print "[Qed.QED]\n" else ()
  (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)

  let rec findMin = function
    | [] -> None
    | O :: L ->
        let rec findMin' = function
          | [], k, result -> result
          | O' :: L', k, result ->
              let k' = Splitting.index O' in
              if Splitting.index O' < k then findMin' (L', k', Some O')
              else findMin' (L', k, result)
        in
        findMin' (L, Splitting.index O, Some O)
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

  let rec split (S :: givenStates, os) =
    match findMin ((Timers.time Timers.splitting Splitting.expand) S) with
    | None -> recurse (givenStates, (S :: openStates, solvedStates))
    | Some splitOp -> (
        let _ = printSplitting () in
        let SL = (Timers.time Timers.splitting Splitting.apply) splitOp in
        let _ = printCloseBracket () in
        try recurse (SL @ givenStates, os)
        with Splitting.Error _ ->
          recurse (givenStates, (S :: openStates, solvedStates)))

  and fill = function
    | [], os -> os
    | S :: givenStates, os -> (
        match (Timers.time Timers.filling Filling.expand) S with
        | _, fillingOp -> (
            try
              let _ = printFilling () in
              let [ S' ] =
                (Timers.time Timers.filling Filling.apply) fillingOp
              in
              let _ = printCloseBracket () in
              if Qed.subgoal S' then (
                printFinish S';
                recurse (givenStates, (openStates, S' :: solvedStates)))
              else fill (S' :: givenStates, os)
            with Filling.Error _ -> split (S :: givenStates, os)))

  and recurse = function
    | [], os -> os
    | S :: givenStates, os -> (
        match (Timers.time Timers.recursion Recursion.expandEager) S with
        | [] -> fill (S :: givenStates, os)
        | recursionOp :: _ -> (
            let _ = printRecursion () in
            let S' =
              (Timers.time Timers.recursion Recursion.apply) recursionOp
            in
            let _ = printCloseBracket () in
            try recurse (S' :: givenStates, (openStates, solvedStates))
            with Recursion.Error _ -> fill (S :: givenStates, os)))
  (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)

  let rec run givenStates =
    let _ = printInit () in
    let os = recurse (givenStates, ([], [])) in
    let _ = match os with [], _ -> printQed () | _ -> () in
    os

  let run = run
  (* local *)
end

(* functor StrategyRFS *)

module Strategy
    (MetaGlobal : Meta_global.METAGLOBAL)
    (MetaSyn' : Metasyn.METASYN)
    (StrategyFRS : STRATEGY)
    (StrategyRFS : STRATEGY) : STRATEGY = struct
  module MetaSyn = MetaSyn'

  let rec run SL =
    match !MetaGlobal.strategy with
    | MetaGlobal.RFS -> StrategyRFS.run SL
    | MetaGlobal.FRS -> StrategyFRS.run SL
end

(* functor Strategy *)
