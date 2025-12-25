open Basis
(* Solve and query declarations, interactive top level *)

(* Author: Frank Pfenning *)

module type SOLVE = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Paths : Paths.PATHS !*)
  module ExtQuery : Recon_query.EXTQUERY

  exception AbortQuery of string

  val solve :
    ExtQuery.define list * ExtQuery.solve * Paths.location ->
    IntSyn.conDec * Paths.occConDec option list

  val query :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val querytabled :
    (int option * int option * ExtQuery.query) * Paths.location -> unit

  (* may raise AbortQuery(msg) *)
  val qLoop : unit -> bool

  (* true means normal exit *)
  val qLoopT : unit -> bool
  (* true means normal exit *)
end

(* signature SOLVE *)
(* Front End Interface *)

(* Author: Frank Pfenning *)

(* Modified: Carsten Schuermann, Jeff Polakow, Roberto Virga *)

module Solve
    (ReconQuery :
      RECON_QUERY
        with type ReconQuery.query = Parser.ExtQuery.query
        with type ReconQuery.solve = Parser.ExtQuery.solve
        with type ReconQuery.define = Parser.ExtQuery.define)
    (Global : Global.GLOBAL)
    (Names : Names.NAMES)
    (Parser : Parse_prg.Parser.PARSER)
    (ReconQuery : Recon_query.RECON_QUERY)
    (Timers : Timers.TIMERS)
    (Compile : Compile.COMPILE)
    (CPrint : Cprint.CPRINT)
    (AbsMachine : Absmachine.ABSMACHINE)
    (AbsMachineSbt : Absmachine.Absmachine_sbt.ABSMACHINESBT)
    (PtRecon : Ptrecon.PTRECON)
    (Tabled : Tabled.Table.TABLED)
    (Print : Print.PRINT)
    (Msg : Msg.MSG) : SOLVE = struct
  (*! structure IntSyn = IntSyn' !*)

  module ExtQuery = ReconQuery
  (*! structure Paths = ReconQuery.Paths !*)

  module S = ParserStream
  (* evarInstToString Xs = msg
     formats instantiated a substitution.
     empty string if chatter level is < 3.
  *)

  let rec evarInstToString Xs =
    if !Global.chatter >= 3 then Print.evarInstToString Xs else ""
  (* expToString (G, U) = msg
     formats a string.
     empty string if chatter level is < 3.
  *)

  let rec expToString GU =
    if !Global.chatter >= 3 then Print.expToString GU else ""
  (* exception AbortQuery
     is raised when a %query declaration has an unexpected number of solutions
     or of %solve has no solution.
  *)

  exception AbortQuery of string
  (* Bounds SOME(n) for_sml n >= 0, NONE represents positive infinity *)

  (* Concrete syntax: 0, 1, 2, ..., * *)

  type bound = int option
  (* exceeds : bound * bound -> bool *)

  let rec exceeds = function
    | Some n, Some m -> n >= m
    | Some n, None -> false
    | None, _ -> true
  (* boundEq : bound * bound -> bool *)

  let rec boundEq = function
    | Some n, Some m -> n = m
    | None, None -> true
    | _ -> false
  (* boundToString : bound -> string *)

  let rec boundToString = function Some n -> Int.toString n | None -> "*"
  (* boundMin : bound * bound -> bound *)

  let rec boundMin = function
    | Some n, Some m -> Some (Int.min (n, m))
    | b, None -> b
    | None, b -> b
  (* checkSolutions : bound * bound * int -> unit *)

  (* raises AbortQuery(msg) if the actual solutions do not match *)

  (* the expected number, given the bound on the number of tries *)

  let rec checkSolutions (expected, try_, solutions) =
    if boundEq (boundMin (expected, try_), Some solutions) then ()
    else
      raise
        (AbortQuery
           ("Query error -- wrong number of solutions: expected "
          ^ boundToString expected ^ " in " ^ boundToString try_
          ^ " tries, but found " ^ Int.toString solutions))
  (* checkStages : bound * int -> unit *)

  (* raises AbortQuery(msg) if the actual #stages do not match *)

  (* the expected number, given the bound on the number of tries *)

  let rec checkStages (try_, stages) =
    if boundEq (try_, Some stages) then ()
    else
      raise
        (AbortQuery
           ("Query error -- wrong number of stages: " ^ boundToString try_
          ^ " tries, but terminated after  " ^ Int.toString stages))
  (* moreSolutions () = b  iff  the user requests more solutions
     Effects: inputs one line from standard input,
              raises exception AbortQuery(msg) is first character is "q" or "Q"
  *)

  let rec moreSolutions () =
    print "More? ";
    match String.sub (Compat.inputLine97 TextIO.stdIn, 0) with
    | 'y' -> true
    | 'Y' -> true
    | ';' -> true
    | 'q' -> raise (AbortQuery "Query error -- explicit quit")
    | 'Q' -> raise (AbortQuery "Query error -- explicit quit")
    | _ -> false
  (* exception Done is raised by the initial success continuation
     when no further solutions are requested.
  *)

  exception Done
  (* exception Completed raised by tabled computation when table is saturated *)

  exception Completed
  (* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *)

  exception Solution of IntSyn.exp
  exception SolutionSkel of CompSyn.pskeleton
  (* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)

  let rec solve' (defines, solve, Paths.Loc (fileName, r)) =
    (* echo declaration, according to chatter level *)
    let A, finish =
      (* self timing *)
      ReconQuery.solveToSolve (defines, solve, Paths.Loc (fileName, r))
    in
    let _ = if !Global.chatter >= 3 then Msg.message "%solve " else () in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("\n"
          ^ (Timers.time Timers.printing expToString) (IntSyn.Null, A)
          ^ ".\n")
      else ()
    in
    let g =
      (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
    in
    let rec search () =
      AbsMachine.solve
        ( (g, IntSyn.id),
          CompSyn.DProg (IntSyn.Null, IntSyn.Null),
          fun M -> raise (Solution M) )
    in
    Cs.CSManager.reset ();
    try
      (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)
      TimeLimit.timeLimit !Global.timeLimit
        (Timers.time Timers.solving search)
        ();
      raise (AbortQuery "No solution to %solve found")
    with Solution M -> (
      try
        if !Global.chatter >= 3 then Msg.message " OK\n" else ();
        finish M
      with TimeLimit.TimeOut ->
        raise (AbortQuery "\n----------- TIME OUT ---------------\n"))
  (* Using substitution tree indexing for_sml clauses in signature
   The logic programming interpreter then creates a proof skeleton
  and reconstructs the actual proof term which can be checked
  -- this version can be used to produce oracles, however no user
  directive is added yet.
*)

  let rec solveSbt (defines, solve, Paths.Loc (fileName, r)) =
    (* echo declaration, according to chatter level *)
    let A, finish =
      (* self timing *)
      ReconQuery.solveToSolve (defines, solve, Paths.Loc (fileName, r))
    in
    let _ = if !Global.chatter >= 3 then Msg.message "%solve " else () in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("\n"
          ^ (Timers.time Timers.printing expToString) (IntSyn.Null, A)
          ^ ".\n")
      else ()
    in
    let g =
      (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
    in
    Cs.CSManager.reset ();
    try
      (* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)
      (TimeLimit.timeLimit !Global.timeLimit)
        (Timers.time Timers.solving AbsMachineSbt.solve)
        ( (g, IntSyn.id),
          CompSyn.DProg (IntSyn.Null, IntSyn.Null),
          fun Skel -> raise (SolutionSkel Skel) );
      raise (AbortQuery "No solution to %solve found")
    with SolutionSkel Skel -> (
      try
        if !Global.chatter >= 2 then Msg.message " OK\n" else ();
        try
          (Timers.time Timers.ptrecon PtRecon.solve)
            ( Skel,
              (g, IntSyn.id),
              CompSyn.DProg (IntSyn.Null, IntSyn.Null),
              fun (Skel, M) -> raise (Solution M) );
          raise (AbortQuery "Proof reconstruction for_sml %solve failed")
        with Solution M -> finish M
      with TimeLimit.TimeOut ->
        raise (AbortQuery "\n----------- TIME OUT ---------------\n"))

  let rec solve args =
    match !Compile.optimize with
    (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *)
    | Compile.Indexing -> solveSbt args
    | Compile.LinearHeads -> solve' args
    | _ -> solve' args
  (* %query <expected> <try> A or %query <expected> <try> X : A *)

  let rec query' ((expected, try_, quy), Paths.Loc (fileName, r)) =
    (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
    (* times itself *)
    (* Problem: we cannot give an answer substitution for_sml the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for_sml the
         original variables encountered during parsing.
       *)
    (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
       *)
    (* solutions = ref <n> counts the number of solutions found *)
    (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for_sml further solutions
       *)
    let A, optName, Xs =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("%query " ^ boundToString expected ^ " " ^ boundToString try_ ^ "\n")
      else ()
    in
    let _ = if !Global.chatter >= 4 then Msg.message " " else () in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("\n"
          ^ (Timers.time Timers.printing expToString) (IntSyn.Null, A)
          ^ ".\n")
      else ()
    in
    let g =
      (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
    in
    let solutions = ref 0 in
    let rec scInit M =
      solutions := !solutions + 1;
      if !Global.chatter >= 3 then (
        Msg.message
          ("---------- Solution " ^ Int.toString !solutions ^ " ----------\n");
        Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ "\n"))
      else if !Global.chatter >= 3 then Msg.message "."
      else ();
      match optName with
      | None -> ()
      | Some name ->
          if !Global.chatter >= 3 then
            Msg.message
              ((Timers.time Timers.printing evarInstToString) [ (M, name) ]
              ^ "\n")
          else ();
          if
            !Global.chatter
            >= 3 (* Question: should we collect constraints in M? *)
          then
            match
              (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
            with
            | None -> ()
            | Some str -> Msg.message ("Remaining constraints:\n" ^ str ^ "\n")
          else ();
          if exceeds (Some !solutions, try_) then raise Done else ()
    in
    let rec search () =
      AbsMachine.solve
        ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit)
    in
    if not (boundEq (try_, Some 0)) then (
      Cs.CSManager.reset ();
      (* solve query if bound > 0 *)
      try
        try
          TimeLimit.timeLimit !Global.timeLimit
            (Timers.time Timers.solving search)
            ()
        with Done -> () (* printing is timed into solving! *)
      with TimeLimit.TimeOut ->
        raise (AbortQuery "\n----------- TIME OUT ---------------\n");
        Cs.CSManager.reset ();
        (* in case Done was raised *)
        (* check if number of solutions is correct *)
        checkSolutions (expected, try_, !solutions))
    else if !Global.chatter >= 3 then Msg.message "Skipping query (bound = 0)\n"
    else if !Global.chatter >= 4 then Msg.message "skipping"
    else ();
    if !Global.chatter >= 3 then
      Msg.message "____________________________________________\n\n"
    else if !Global.chatter >= 4 then Msg.message " OK\n"
    else ()
  (* %query <expected> <try> A or %query <expected> <try> X : A *)

  let rec querySbt ((expected, try_, quy), Paths.Loc (fileName, r)) =
    (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
    (* times itself *)
    (* Problem: we cannot give an answer substitution for_sml the variables
               in the printed query, since the new variables in this query
               may not necessarily have global scope.

               For the moment, we print only the answer substitution for_sml the
               original variables encountered during parsing.
             *)
    (*
                val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
             *)
    (* solutions = ref <n> counts the number of solutions found *)
    (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for_sml further solutions
       *)
    let A, optName, Xs =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("%query " ^ boundToString expected ^ " " ^ boundToString try_ ^ "\n")
      else ()
    in
    let _ = if !Global.chatter >= 4 then Msg.message " " else () in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("\n"
          ^ (Timers.time Timers.printing expToString) (IntSyn.Null, A)
          ^ ".\n")
      else ()
    in
    let g =
      (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
    in
    let solutions = ref 0 in
    let rec scInit M =
      solutions := !solutions + 1;
      if !Global.chatter >= 3 then (
        Msg.message
          ("---------- Solution " ^ Int.toString !solutions ^ " ----------\n");
        Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ "\n"))
      else if !Global.chatter >= 3 then Msg.message "."
      else ();
      match optName with
      | None -> ()
      | Some name ->
          if !Global.chatter > 3 then (
            Msg.message "\n pskeleton \n";
            Msg.message (CompSyn.pskeletonToString M ^ "\n"))
          else ();
          (Timers.time Timers.ptrecon PtRecon.solve)
            ( M,
              (g, IntSyn.id),
              CompSyn.DProg (IntSyn.Null, IntSyn.Null),
              fun (pskel, M) ->
                if !Global.chatter >= 3 then
                  Msg.message
                    ((Timers.time Timers.printing evarInstToString)
                       [ (M, name) ]
                    ^ "\n")
                else () );
          if
            !Global.chatter
            >= 3 (* Question: should we collect constraints in M? *)
          then
            match
              (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
            with
            | None -> ()
            | Some str -> Msg.message ("Remaining constraints:\n" ^ str ^ "\n")
          else ();
          if exceeds (Some !solutions, try_) then raise Done else ()
    in
    let rec search () =
      AbsMachineSbt.solve
        ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit)
    in
    if not (boundEq (try_, Some 0)) then (
      Cs.CSManager.reset ();
      (* solve query if bound > 0 *)
      try
        TimeLimit.timeLimit !Global.timeLimit
          (Timers.time Timers.solving search)
          ()
      with Done -> (
        try ()
        with TimeLimit.TimeOut ->
          raise (AbortQuery "\n----------- TIME OUT ---------------\n");
          (* printing is timed into solving! *)
          Cs.CSManager.reset ();
          (* in case Done was raised *)
          (* check if number of solutions is correct *)
          checkSolutions (expected, try_, !solutions)))
    else if !Global.chatter >= 3 then Msg.message "Skipping query (bound = 0)\n"
    else if !Global.chatter >= 4 then Msg.message "skipping"
    else ();
    if !Global.chatter >= 3 then
      Msg.message "____________________________________________\n\n"
    else if !Global.chatter >= 4 then Msg.message " OK\n"
    else ()
  (* %query <expected> <try> A or %query <expected> <try> X : A  *)

  let rec query args =
    match !Compile.optimize with
    (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *)
    | Compile.Indexing -> querySbt args
    | Compile.LinearHeads -> query' args
    | _ -> query' args
  (* %querytabled <expected solutions> <max stages tried>  A
or  %querytabled <expected solutions> <max stages tried>  X : A
  note : %querytabled terminates if we have found the expected number of
  solutions or if we have reached the maximal number of stages *)

  let rec querytabled ((numSol, try_, quy), Paths.Loc (fileName, r)) =
    (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
    (* times itself *)
    (* Problem: we cannot give an answer substitution for_sml the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for_sml the
        original variables encountered during parsing.
     *)
    (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *)
    (* solutions = ref <n> counts the number of solutions found *)
    (* stage = ref <n> counts the number of stages found *)
    (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for_sml further solutions
       *)
    (* loops -- scinit will raise exception Done *)
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("%querytabled " ^ boundToString numSol ^ " " ^ boundToString try_)
      else ()
    in
    let A, optName, Xs =
      ReconQuery.queryToQuery (quy, Paths.Loc (fileName, r))
    in
    let _ = if !Global.chatter >= 4 then Msg.message " " else () in
    let _ =
      if !Global.chatter >= 3 then
        Msg.message
          ("\n"
          ^ (Timers.time Timers.printing expToString) (IntSyn.Null, A)
          ^ ".\n")
      else ()
    in
    let g =
      (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
    in
    let solutions = ref 0 in
    let status = ref false in
    let solExists = ref false in
    let stages = ref 1 in
    let rec scInit O =
      solutions := !solutions + 1;
      solExists := true;
      if !Global.chatter >= 3 then (
        Msg.message
          ("\n---------- Solutions " ^ Int.toString !solutions ^ " ----------\n");
        Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ " \n"))
      else if !Global.chatter >= 1 then Msg.message "."
      else ();
      (match optName with
      | None -> ()
      | Some name ->
          Msg.message (CompSyn.pskeletonToString O ^ "\n");
          (Timers.time Timers.ptrecon PtRecon.solve)
            ( O,
              (g, IntSyn.id),
              CompSyn.DProg (IntSyn.Null, IntSyn.Null),
              fun (O, M) ->
                if !Global.chatter >= 3 then
                  Msg.message
                    ((Timers.time Timers.printing evarInstToString)
                       [ (M, name) ]
                    ^ "\n")
                else () ));
      if !Global.chatter >= 3 then
        (* Question: should we collect constraints in M? *)
        match (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs with
        | None -> ()
        | Some str -> Msg.message ("Remaining constraints:\n" ^ str ^ "\n")
      else ();
      if !Global.chatter >= 1 then Msg.message "More solutions?\n" else ();
      match numSol with
      | None -> ()
      | Some n ->
          if !solutions = n then (
            if !Global.chatter >= 1 then Msg.message "Found enough solutions\n"
            else ();
            raise Done)
          else ()
    in
    let rec loop () =
      if exceeds (Some (!stages - 1), try_) then (
        if !Global.chatter >= 1 then
          Msg.message
            ("\n ================= " ^ " Number of tries exceeds stages "
           ^ " ======================= \n")
        else ();
        status := false;
        raise Done)
      else ();
      if !Global.chatter >= 1 then
        Msg.message
          ("\n ====================== Stage " ^ Int.toString !stages
         ^ " finished =================== \n")
      else ();
      if exceeds (Some !stages, try_) then (
        Msg.message
          ("\n ================= " ^ " Number of tries exceeds stages "
         ^ " ======================= \n");
        status := false;
        raise Done)
      else ();
      if Tabled.nextStage () then (
        stages := !stages + 1;
        loop ())
      else
        (* table did not change,
         * i.e. all solutions have been found
         * we check for_sml *all* solutions
         *)
        status := true;
      raise Done
    in
    let _ = Tabled.reset () in
    let _ = Tabled.fillTable () in
    let rec tabledSearch () =
      Tabled.solve
        ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit);
      Cs.CSManager.reset ();
      (* in case Done was raised *)
      (* next stage until table doesn't change *)
      loop ();
      checkStages (try_, !stages)
    in
    if not (boundEq (try_, Some 0)) then
      try
        Cs.CSManager.reset ();
        (* solve query if bound > 0 *)
        try
          TimeLimit.timeLimit !Global.timeLimit
            (Timers.time Timers.solving tabledSearch)
            ()
        with TimeLimit.TimeOut ->
          Msg.message "\n----------- TIME OUT ---------------\n";
          raise Done
      with Done -> ()
    else if !Global.chatter >= 3 then Msg.message "Skipping query (bound = 0)\n"
    else if !Global.chatter >= 2 then Msg.message "skipping"
    else ();
    if !Global.chatter >= 3 then (
      Msg.message "\n____________________________________________\n\n";
      Msg.message
        ("number of stages: tried " ^ boundToString try_ ^ " \n"
       ^ "terminated after " ^ Int.toString !stages ^ " stages \n \n");
      if !solExists then ()
      else Msg.message "\nNO solution exists to query \n\n";
      if !status then Msg.message "Tabled evaluation COMPLETE \n \n"
      else Msg.message "Tabled evaluation NOT COMPLETE \n \n";
      Msg.message "\n____________________________________________\n\n";
      Msg.message "\n Table Indexing parameters: \n";
      match !TableParam.strategy with
      | TableParam.Variant ->
          Msg.message "\n       Table Strategy := Variant \n"
      | TableParam.Subsumption ->
          Msg.message "\n       Table Strategy := Subsumption \n";
          if !TableParam.strengthen then
            Msg.message "\n       Strengthening := true \n"
          else Msg.message "\n       Strengthening := false \n";
          Msg.message
            ("\nNumber of table indices : "
            ^ Int.toString (Tabled.tableSize ())
            ^ "\n");
          Msg.message
            ("Number of suspended goals : "
            ^ Int.toString (Tabled.suspGoalNo ())
            ^ "\n");
          Msg.message "\n____________________________________________\n\n")
    else if !Global.chatter >= 3 then Msg.message " OK\n"
    else ();
    Tabled.updateGlobalTable (g, !status)
  (* Interactive Query Top Level *)

  let rec qLoop () =
    qLoops
      (Cs.CSManager.reset ();
       Parser.parseTerminalQ ("?- ", "   "))

  and qLoops s = qLoops' ((Timers.time Timers.parsing S.expose) s)

  and qLoops' = function
    | S.Empty -> true
    | S.Cons (query, s') -> (
        (* times itself *)
        let A, optName, Xs =
          ReconQuery.queryToQuery (query, Paths.Loc ("stdIn", Paths.Reg (0, 0)))
        in
        let g =
          (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
        in
        let rec scInit M =
          if !Global.chatter >= 1 then
            Msg.message
              ((Timers.time Timers.printing evarInstToString) Xs ^ "\n")
          else ();
          match optName with
          | None -> ()
          | Some name ->
              if !Global.chatter >= 3 then
                Msg.message
                  ((Timers.time Timers.printing evarInstToString) [ (M, name) ]
                  ^ "\n")
              else ();
              if
                !Global.chatter
                >= 3 (* Question: should we collect constraints from M *)
              then
                match
                  (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
                with
                | None -> ()
                | Some str ->
                    Msg.message ("Remaining constraints:\n" ^ str ^ "\n")
              else ();
              if moreSolutions () then () else raise Done
        in
        let _ =
          if !Global.chatter >= 3 then Msg.message "Solving...\n" else ()
        in
        try
          (Timers.time Timers.solving AbsMachine.solve)
            ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit);
          (* scInit is timed into solving! *)
          Msg.message "No more solutions\n"
        with Done ->
          ();
          (* Ignore s': parse one query at a time *)
          qLoop ())
  (* querytabled interactive top loop *)

  let rec qLoopT () =
    qLoopsT
      (Cs.CSManager.reset ();
       Parser.parseTerminalQ ("?- ", "   "))

  and qLoopsT s = qLoopsT' ((Timers.time Timers.parsing S.expose) s)

  and qLoopsT' = function
    | S.Empty -> true
    | S.Cons (query, s') -> (
        (* times itself *)
        (* loops -- scinit will raise exception Done *)
        let solExists = ref false in
        let A, optName, Xs =
          ReconQuery.queryToQuery (query, Paths.Loc ("stdIn", Paths.Reg (0, 0)))
        in
        let g =
          (Timers.time Timers.compiling Compile.compileGoal) (IntSyn.Null, A)
        in
        let _ = Tabled.reset () in
        let rec scInit O =
          if !Global.chatter >= 1 then
            Msg.message
              ((Timers.time Timers.printing evarInstToString) Xs ^ "\n")
          else ();
          match optName with
          | None -> ()
          | Some name ->
              if !Global.chatter >= 3 then
                Msg.message
                  " Sorry cannot reconstruct pskeleton proof terms yet \n"
              else ();
              if
                !Global.chatter
                >= 3 (* Question: should we collect constraints from M? *)
              then
                match
                  (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
                with
                | None -> ()
                | Some str ->
                    Msg.message ("Remaining constraints:\n" ^ str ^ "\n")
              else ();
              solExists := true;
              if moreSolutions () then () else raise Done
        in
        let rec loop () =
          if Tabled.nextStage () then loop ()
          else
            (* table did not change,
             * i.e. all solutions have been found
             * we check for_sml *all* solutions
             *)
            raise Completed
        in
        let _ =
          if !Global.chatter >= 3 then Msg.message "Solving...\n" else ()
        in
        try
          (Timers.time Timers.solving Tabled.solve)
            ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit);
          (* scInit is timed into solving! *)
          try loop ()
          with Completed ->
            if !solExists then Msg.message "No more solutions\n"
            else Msg.message "the query has no solution\n"
        with Done ->
          ();
          (* Ignore s': parse one query at a time *)
          qLoopT ())
end

(* functor Solve *)
