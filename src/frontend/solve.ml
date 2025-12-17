Solve  Global GLOBAL    Names NAMES    Parser PARSER    Parser Names  Names   ReconQuery RECON_QUERY     Query Query   Solve Solve   Define Define  Timers TIMERS    Compile COMPILE    CPrint CPRINT    AbsMachine ABSMACHINE    AbsMachineSbt ABSMACHINESBT    PtRecon PTRECON    Tabled TABLED    Print PRINT    Msg MSG     SOLVE  struct (*! structure IntSyn = IntSyn' !*)
module (*! structure Paths = ReconQuery.Paths !*)
module (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
let rec evarInstToString(xs) if ! chatter >= 3 then evarInstToString (xs) else ""(* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
let rec expToStringgU if ! chatter >= 3 then expToString gU else ""(* exception AbortQuery
     is raised when a %query declaration has an unexpected number of solutions
     or of %solve has no solution.
  *)
exception (* Bounds SOME(n) for n >= 0, NONE represents positive infinity *)
(* Concrete syntax: 0, 1, 2, ..., * *)
type Bound(* exceeds : bound * bound -> bool *)
let rec exceeds(sOME (n),  , sOME (m)) (n >= m) exceeds(sOME (n),  , nONE) false exceeds(nONE,  , _) true(* boundEq : bound * bound -> bool *)
let rec boundEq(sOME (n),  , sOME (m)) (n = m) boundEq(nONE,  , nONE) true boundEq_ false(* boundToString : bound -> string *)
let rec boundToString(sOME (n)) toString (n) boundToString(nONE) "*"(* boundMin : bound * bound -> bound *)
let rec boundMin(sOME (n),  , sOME (m)) sOME (min (n,  , m)) boundMin(b,  , nONE) b boundMin(nONE,  , b) b(* checkSolutions : bound * bound * int -> unit *)
(* raises AbortQuery(msg) if the actual solutions do not match *)
(* the expected number, given the bound on the number of tries *)
let rec checkSolutions(expected,  , try,  , solutions) if boundEq (boundMin (expected,  , try),  , sOME (solutions)) then () else raise (abortQuery ("Query error -- wrong number of solutions: expected " ^ boundToString expected ^ " in " ^ boundToString try ^ " tries, but found " ^ toString solutions))(* checkStages : bound * int -> unit *)
(* raises AbortQuery(msg) if the actual #stages do not match *)
(* the expected number, given the bound on the number of tries *)
let rec checkStages(try,  , stages) if boundEq (try,  , sOME (stages)) then () else raise (abortQuery ("Query error -- wrong number of stages: " ^ boundToString try ^ " tries, but terminated after  " ^ toString stages))(* moreSolutions () = b  iff  the user requests more solutions
     Effects: inputs one line from standard input,
              raises exception AbortQuery(msg) is first character is "q" or "Q"
  *)
let rec moreSolutions() (print ("More? "); match sub (inputLine97 (stdIn),  , 0) with 'y' -> true 'Y' -> true ';' -> true 'q' -> raise (abortQuery ("Query error -- explicit quit")) 'Q' -> raise (abortQuery ("Query error -- explicit quit")) _ -> false)(* exception Done is raised by the initial success continuation
     when no further solutions are requested.
  *)
exception (* exception Completed raised by tabled computation when table is saturated *)
exception (* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *)
exception exception (* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)
let rec solve'(defines,  , solve,  , loc (fileName,  , r)) let let  in(* echo declaration, according to chatter level *)
let  inlet  inlet  inlet rec search() solve ((g,  , id),  , dProg (null,  , null),  , fun m -> raise (solution m)) in reset ()try  with (* Using substitution tree indexing for clauses in signature
   The logic programming interpreter then creates a proof skeleton
  and reconstructs the actual proof term which can be checked
  -- this version can be used to produce oracles, however no user
  directive is added yet.
*)
let rec solveSbt(defines,  , solve,  , loc (fileName,  , r)) let let  in(* echo declaration, according to chatter level *)
let  inlet  inlet  in in reset ()try  with let rec solveargs match (! optimize) with (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *)
indexing -> solveSbt args linearHeads -> solve' args _ -> solve' args(* %query <expected> <try> A or %query <expected> <try> X : A *)
let rec query'((expected,  , try,  , quy),  , loc (fileName,  , r)) let (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
let  in(* times itself *)
let  inlet  inlet  in(* Problem: we cannot give an answer substitution for the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for the
         original variables encountered during parsing.
       *)
(* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
       *)
let  in(* solutions = ref <n> counts the number of solutions found *)
let  in(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
let rec scInitm (solutions := ! solutions + 1; if ! chatter >= 3 then (message ("---------- Solution " ^ toString (! solutions) ^ " ----------\n"); message ((time printing evarInstToString) xs ^ "\n")) else if ! chatter >= 3 then message "." else (); match optName with nONE -> () sOME (name) -> if ! chatter >= 3 then message ((time printing evarInstToString) [(m,  , name)] ^ "\n") else (); if ! chatter >= 3(* Question: should we collect constraints in M? *)
 then match (time printing evarCnstrsToStringOpt) xs with nONE -> () sOME (str) -> message ("Remaining constraints:\n" ^ str ^ "\n") else (); if exceeds (sOME (! solutions),  , try) then raise (done) else ())let rec search() solve ((g,  , id),  , dProg (null,  , null),  , scInit) in if not (boundEq (try,  , sOME (0))) then (reset (); (* solve query if bound > 0 *)
try  with ; reset (); (* in case Done was raised *)
(* check if number of solutions is correct *)
checkSolutions (expected,  , try,  , ! solutions)) else if ! chatter >= 3 then message ("Skipping query (bound = 0)\n") else if ! chatter >= 4 then message ("skipping") else ()if ! chatter >= 3 then message "____________________________________________\n\n" else if ! chatter >= 4 then message (" OK\n") else ()(* %query <expected> <try> A or %query <expected> <try> X : A *)
let rec querySbt((expected,  , try,  , quy),  , loc (fileName,  , r)) let (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
let  in(* times itself *)
let  inlet  inlet  in(* Problem: we cannot give an answer substitution for the variables
               in the printed query, since the new variables in this query
               may not necessarily have global scope.

               For the moment, we print only the answer substitution for the
               original variables encountered during parsing.
             *)
(*
                val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
             *)
let  in(* solutions = ref <n> counts the number of solutions found *)
let  in(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
let rec scInitm (solutions := ! solutions + 1; if ! chatter >= 3 then (message ("---------- Solution " ^ toString (! solutions) ^ " ----------\n"); message ((time printing evarInstToString) xs ^ "\n")) else if ! chatter >= 3 then message "." else (); match optName with nONE -> () sOME (name) -> (if ! chatter > 3 then (message ("\n pskeleton \n"); message ((pskeletonToString m) ^ "\n")) else (); (time ptrecon solve) (m,  , (g,  , id),  , dProg (null,  , null),  , (fun (pskel,  , m) -> (if ! chatter >= 3 then message ((time printing evarInstToString) [(m,  , name)] ^ "\n") else ())))); if ! chatter >= 3(* Question: should we collect constraints in M? *)
 then match (time printing evarCnstrsToStringOpt) xs with nONE -> () sOME (str) -> message ("Remaining constraints:\n" ^ str ^ "\n") else (); if exceeds (sOME (! solutions),  , try) then raise (done) else ())let rec search() solve ((g,  , id),  , dProg (null,  , null),  , scInit) in if not (boundEq (try,  , sOME (0))) then (reset (); (* solve query if bound > 0 *)
try  with ; (* printing is timed into solving! *)
reset (); (* in case Done was raised *)
(* check if number of solutions is correct *)
checkSolutions (expected,  , try,  , ! solutions)) else if ! chatter >= 3 then message ("Skipping query (bound = 0)\n") else if ! chatter >= 4 then message ("skipping") else ()if ! chatter >= 3 then message "____________________________________________\n\n" else if ! chatter >= 4 then message (" OK\n") else ()(* %query <expected> <try> A or %query <expected> <try> X : A  *)
let rec queryargs match (! optimize) with (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *)
indexing -> querySbt args linearHeads -> query' args _ -> query' args(* %querytabled <expected solutions> <max stages tried>  A
or  %querytabled <expected solutions> <max stages tried>  X : A
  note : %querytabled terminates if we have found the expected number of
  solutions or if we have reached the maximal number of stages *)
let rec querytabled((numSol,  , try,  , quy),  , loc (fileName,  , r)) let let  in(* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
let  in(* times itself *)
let  inlet  in(* Problem: we cannot give an answer substitution for the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for the
        original variables encountered during parsing.
     *)
(* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *)
let  in(* solutions = ref <n> counts the number of solutions found *)
let  inlet  inlet  in(* stage = ref <n> counts the number of stages found *)
let  in(* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
let rec scInito (solutions := ! solutions + 1; solExists := true; if ! chatter >= 3 then (message ("\n---------- Solutions " ^ toString (! solutions) ^ " ----------\n"); message ((time printing evarInstToString) xs ^ " \n")) else if ! chatter >= 1 then message "." else (); (match optName with nONE -> () sOME (name) -> (message (pskeletonToString o ^ "\n"); (time ptrecon solve) (o,  , (g,  , id),  , dProg (null,  , null),  , (fun (o,  , m) -> if ! chatter >= 3 then message ((time printing evarInstToString) [(m,  , name)] ^ "\n") else ())))); (if ! chatter >= 3 then (* Question: should we collect constraints in M? *)
match (time printing evarCnstrsToStringOpt) xs with nONE -> () sOME (str) -> message ("Remaining constraints:\n" ^ str ^ "\n") else ()); (if ! chatter >= 1 then message "More solutions?\n" else ()); match numSol with nONE -> () sOME n -> (if (! solutions = n) then ((if ! chatter >= 1 then message "Found enough solutions\n" else ()); raise (done)) else ()))(* loops -- scinit will raise exception Done *)
let rec loop() (if exceeds (sOME (! stages - 1),  , try) then ((if ! chatter >= 1 then message ("\n ================= " ^ " Number of tries exceeds stages " ^ " ======================= \n") else ()); status := false; raise (done)) else (); (if ! chatter >= 1 then message ("\n ====================== Stage " ^ toString (! stages) ^ " finished =================== \n") else ()); if exceeds (sOME (! stages),  , try) then (message ("\n ================= " ^ " Number of tries exceeds stages " ^ " ======================= \n"); status := false; raise (done)) else (); if nextStage () then (stages := (! stages) + 1; loop ()) else (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)
status := true; raise (done))let  inlet  inlet rec tabledSearch() (solve ((g,  , id),  , dProg (null,  , null),  , scInit); reset (); (* in case Done was raised *)
(* next stage until table doesn't change *)
loop (); checkStages (try,  , ! stages)) in if not (boundEq (try,  , sOME (0))) then try  with  else if ! chatter >= 3 then message ("Skipping query (bound = 0)\n") else if ! chatter >= 2 then message ("skipping") else ()if ! chatter >= 3 then (message "\n____________________________________________\n\n"; message ("number of stages: tried " ^ boundToString try ^ " \n" ^ "terminated after " ^ toString (! stages) ^ " stages \n \n"); if (! solExists) then () else message "\nNO solution exists to query \n\n"; if (! status) then message "Tabled evaluation COMPLETE \n \n" else message "Tabled evaluation NOT COMPLETE \n \n"; message "\n____________________________________________\n\n"; message "\n Table Indexing parameters: \n"; match (! strategy) with variant -> message "\n       Table Strategy := Variant \n" subsumption -> message "\n       Table Strategy := Subsumption \n"; if (! strengthen) then message "\n       Strengthening := true \n" else message "\n       Strengthening := false \n"; message ("\nNumber of table indices : " ^ toString (tableSize ()) ^ "\n"); message ("Number of suspended goals : " ^ toString (suspGoalNo ()) ^ "\n"); message "\n____________________________________________\n\n") else (if ! chatter >= 3 then message (" OK\n") else ())updateGlobalTable (g,  , ! status)(* Interactive Query Top Level *)
let rec qLoop() qLoops (reset (); parseTerminalQ ("?- ",  , "   "))(* primary, secondary prompt *)
 qLoops(s) qLoops' ((time parsing expose) s) qLoops'(empty) true qLoops'(cons (query,  , s')) let let  in(* times itself *)
let  inlet rec scInitm ((if ! chatter >= 1 then message ((time printing evarInstToString) xs ^ "\n") else ()); match optName with nONE -> () sOME (name) -> if ! chatter >= 3 then message ((time printing evarInstToString) [(m,  , name)] ^ "\n") else (); if ! chatter >= 3(* Question: should we collect constraints from M *)
 then match (time printing evarCnstrsToStringOpt) xs with nONE -> () sOME (str) -> message ("Remaining constraints:\n" ^ str ^ "\n") else (); if moreSolutions () then () else raise (done))let  in in try  with (* Ignore s': parse one query at a time *)
qLoop ()(* querytabled interactive top loop *)
let rec qLoopT() qLoopsT (reset (); parseTerminalQ ("?- ",  , "   "))(* primary, secondary prompt *)
 qLoopsT(s) qLoopsT' ((time parsing expose) s) qLoopsT'(empty) true qLoopsT'(cons (query,  , s')) let let  inlet  in(* times itself *)
let  inlet  inlet rec scInito ((if ! chatter >= 1 then message ((time printing evarInstToString) xs ^ "\n") else ()); match optName with nONE -> () sOME (name) -> if ! chatter >= 3 then message (" Sorry cannot reconstruct pskeleton proof terms yet \n") else (); if ! chatter >= 3(* Question: should we collect constraints from M? *)
 then match (time printing evarCnstrsToStringOpt) xs with nONE -> () sOME (str) -> message ("Remaining constraints:\n" ^ str ^ "\n") else (); solExists := true; if moreSolutions () then () else raise (done))(* loops -- scinit will raise exception Done *)
let rec loop() (if nextStage () then loop () else (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)
raise (completed))let  in in try  with (* Ignore s': parse one query at a time *)
qLoopT ()end