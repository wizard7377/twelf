(* GEN BEGIN SIGNATURE DECLARATION *) signature SERVER =
sig

  val server : string * string list -> OS.Process.status

end (* GEN END SIGNATURE DECLARATION *)  (* signature SERVER *)

functor (* GEN BEGIN FUNCTOR DECL *) Server
  (structure SigINT : SIGINT
   structure Timing : TIMING
   structure Lexer : LEXER
   structure Twelf : TWELF)
  :> SERVER =
struct

  (* GEN BEGIN TAG OUTSIDE LET *) val globalConfig : Twelf.Config.config option ref = ref NONE (* GEN END TAG OUTSIDE LET *)

  (* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)
  fun readLine () =
      let
        (* val line = TextIO.inputLine (TextIO.stdIn) *)
  	(* Fix for MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *)
  	fun getLine () = Compat.inputLine97 (TextIO.stdIn)
  	                 handle OS.SysErr (_, SOME _) => getLine ()
  	(* GEN BEGIN TAG OUTSIDE LET *) val line = getLine () (* GEN END TAG OUTSIDE LET *)
        fun triml ss = Substring.dropl Char.isSpace ss
        fun trimr ss = Substring.dropr Char.isSpace ss
        (* GEN BEGIN TAG OUTSIDE LET *) val line' = triml (trimr (Compat.Substring.full line)) (* GEN END TAG OUTSIDE LET *)
      in
  	if line = ""
  	  then ("OS.exit", "")
  	else if Substring.size (line') = 0
  	  then readLine ()
        else
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val (command', args') = Substring.position " " line' (* GEN END TAG OUTSIDE LET *)
          in
            (Substring.string command',
             Substring.string (triml args'))
  	  end
      end
  
  (* tokenize (args) = [token1, token2, ..., tokenn]
     splits the arguments string into a list of space-separated
     tokens
  *)
  fun tokenize (args) = String.tokens Char.isSpace args

  (* exception Error for server errors *)
  exception Error of string
  fun error (msg) = raise Error(msg)

  fun quote (string) = "`" ^ string ^ "'"

  (* Print the OK or ABORT messages which are parsed by Emacs *)
  fun (* GEN BEGIN FUN FIRST *) issue (Twelf.OK) = print ("%% OK %%\n") (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) issue (Twelf.ABORT) = print ("%% ABORT %%\n") (* GEN END FUN BRANCH *)

  (* Checking if there are no extraneous arguments *)
  fun (* GEN BEGIN FUN FIRST *) checkEmpty ("") = () (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) checkEmpty (args) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  (* Command argument types *)
  (* File names, given a default *)
  fun (* GEN BEGIN FUN FIRST *) getFile ("", default) = default (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getFile (fileName, default) = fileName (* GEN END FUN BRANCH *)

  (* File names, not defaults *)
  fun (* GEN BEGIN FUN FIRST *) getFile' ("") = error "Missing filename" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getFile' (fileName) = fileName (* GEN END FUN BRANCH *)

  (* Identifiers, used as a constant *)
  fun (* GEN BEGIN FUN FIRST *) getId (id::nil) = id (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getId (nil) = error "Missing identifier" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getId (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  (* Identifiers, used as a trace specification *)
  fun getIds (ids) = ids

  (* Strategies for %prove, %establish *)
  fun (* GEN BEGIN FUN FIRST *) getStrategy ("FRS"::nil) = Twelf.Prover.FRS (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getStrategy ("RFS"::nil) = Twelf.Prover.RFS (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getStrategy (nil) = error "Missing strategy" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getStrategy (t::nil) = error (quote t ^ " is not a strategy (must be FRS or RFS)") (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getStrategy (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) strategyToString (Twelf.Prover.FRS) = "FRS" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) strategyToString (Twelf.Prover.RFS) = "RFS" (* GEN END FUN BRANCH *)

  (* Booleans *)
  fun (* GEN BEGIN FUN FIRST *) getBool ("true"::nil) = true (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getBool ("false"::nil) = false (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getBool (nil) = error "Missing boolean value" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getBool (t::nil) = error (quote t ^ " is not a boolean") (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getBool (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  (* Natural numbers *)
  fun (* GEN BEGIN FUN FIRST *) getNat (t::nil) =
        (Lexer.stringToNat t
  	 handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number")) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getNat (nil) = error "Missing natural number" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getNat (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  (* Limits ( *, or natural number) *)
  fun (* GEN BEGIN FUN FIRST *) getLimit ("*"::nil) = NONE (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getLimit (t::ts) = SOME (getNat (t::ts)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getLimit (nil) = error "Missing `*' or natural number" (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) limitToString (NONE) = "*" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) limitToString (SOME(i)) = Int.toString i (* GEN END FUN BRANCH *)

  (* Tabling strategy *)
  fun (* GEN BEGIN FUN FIRST *) getTableStrategy ("Variant"::nil) = Twelf.Table.Variant (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getTableStrategy ("Subsumption"::nil) = Twelf.Table.Subsumption (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getTableStrategy (nil) = error "Missing tabling strategy" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getTableStrategy (t::nil) = error (quote t ^ " is not a tabling strategy (must be Variant or Subsumption)") (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getTableStrategy (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) tableStrategyToString (Twelf.Table.Variant) = "Variant" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) tableStrategyToString (Twelf.Table.Subsumption) = "Subsumption" (* GEN END FUN BRANCH *)

  (* Tracing mode for term reconstruction *)
  fun (* GEN BEGIN FUN FIRST *) getReconTraceMode ("Progressive"::nil) = Twelf.Recon.Progressive (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getReconTraceMode ("Omniscient"::nil) = Twelf.Recon.Omniscient (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getReconTraceMode (nil) = error "Missing tracing reconstruction mode" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getReconTraceMode (t::nil) = error (quote t ^ " is not a tracing reconstruction mode\n(must be Progressive or Omniscient)") (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getReconTraceMode (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) reconTraceModeToString (Twelf.Recon.Progressive) = "Progressive" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) reconTraceModeToString (Twelf.Recon.Omniscient) = "Omniscient" (* GEN END FUN BRANCH *)


  (* Compile options *)
  fun (* GEN BEGIN FUN FIRST *) getCompileOpt ("No"::nil) = Twelf.Compile.No (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getCompileOpt ("LinearHeads"::nil) = Twelf.Compile.LinearHeads (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getCompileOpt ("Indexing"::nil) = Twelf.Compile.Indexing (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getCompileOpt (nil) = error "Missing tabling strategy" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getCompileOpt (t::nil) = error (quote t ^ " is not a compile option (must be No, LinearHeads, or Indexing ") (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getCompileOpt (ts) = error "Extraneous arguments" (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) compOptToString (Twelf.Compile.No) = "No" (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) compOptToString (Twelf.Compile.LinearHeads) = "LinearHeads" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) compOptToString (Twelf.Compile.Indexing) = "Indexing" (* GEN END FUN BRANCH *)

  (* Setting Twelf parameters *)
  fun (* GEN BEGIN FUN FIRST *) setParm ("chatter"::ts) = Twelf.chatter := getNat ts (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("doubleCheck"::ts) = Twelf.doubleCheck := getBool ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("unsafe"::ts) = Twelf.unsafe := getBool ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("autoFreeze"::ts) = Twelf.autoFreeze := getBool ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Print.implicit"::ts) = Twelf.Print.implicit := getBool ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Print.depth"::ts) = Twelf.Print.depth := getLimit ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Print.length"::ts) = Twelf.Print.length := getLimit ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Print.indent"::ts) = Twelf.Print.indent := getNat ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Print.width"::ts) = Twelf.Print.width := getNat ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Trace.detail"::ts) = Twelf.Trace.detail := getNat ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Compile.optimize"::ts) = Twelf.Compile.optimize := getCompileOpt ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Recon.trace"::ts) = Twelf.Recon.trace := getBool ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Recon.traceMode"::ts) = Twelf.Recon.traceMode := getReconTraceMode ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Prover.strategy"::ts) = Twelf.Prover.strategy := getStrategy ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Prover.maxSplit"::ts) = Twelf.Prover.maxSplit := getNat ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Prover.maxRecurse"::ts) = Twelf.Prover.maxRecurse := getNat ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Table.strategy"::ts) = Twelf.Table.strategy := getTableStrategy ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm ("Table.strengthen"::ts) = Twelf.Table.strengthen := getBool ts (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm (t::ts) = error ("Unknown parameter " ^ quote t) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) setParm (nil) = error ("Missing parameter") (* GEN END FUN BRANCH *)

  (* Getting Twelf parameter values *)
  fun (* GEN BEGIN FUN FIRST *) getParm ("chatter"::ts) = Int.toString (!Twelf.chatter) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("doubleCheck"::ts) = Bool.toString (!Twelf.doubleCheck) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("unsafe"::ts) = Bool.toString (!Twelf.unsafe) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("autoFreeze"::ts) = Bool.toString (!Twelf.autoFreeze) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Print.implicit"::ts) = Bool.toString (!Twelf.Print.implicit) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Print.depth"::ts) = limitToString (!Twelf.Print.depth) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Print.length"::ts) = limitToString (!Twelf.Print.length) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Print.indent"::ts) = Int.toString (!Twelf.Print.indent) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Print.width"::ts) = Int.toString (!Twelf.Print.width) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Trace.detail"::ts) = Int.toString (!Twelf.Trace.detail) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Compile.optimize"::ts) = compOptToString (!Twelf.Compile.optimize) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Recon.trace"::ts) = Bool.toString (!Twelf.Recon.trace) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Recon.traceMode"::ts) = reconTraceModeToString (!Twelf.Recon.traceMode) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Prover.strategy"::ts) = strategyToString (!Twelf.Prover.strategy) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Prover.maxSplit"::ts) = Int.toString (!Twelf.Prover.maxSplit) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm ("Prover.maxRecurse"::ts) = Int.toString (!Twelf.Prover.maxRecurse) (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) getParm ("Table.strategy"::ts) = tableStrategyToString (!Twelf.Table.strategy) (* GEN END FUN BRANCH *) 
    | (* GEN BEGIN FUN BRANCH *) getParm (t::ts) = error ("Unknown parameter " ^ quote t) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) getParm (nil) = error ("Missing parameter") (* GEN END FUN BRANCH *)

  (* extracted from doc/guide/twelf.texi *)
  (* GEN BEGIN TAG OUTSIDE LET *) val helpString =
  "Commands:\n\
  \  set <parameter> <value>     - Set <parameter> to <value>\n\
  \  get <parameter>             - Print the current value of <parameter>\n\
  \  Trace.trace <id1> ... <idn> - Trace given constants\n\
  \  Trace.traceAll              - Trace all constants\n\
  \  Trace.untrace               - Untrace all constants\n\
  \  Trace.break <id1> ... <idn> - Set breakpoint for given constants\n\
  \  Trace.breakAll              - Break on all constants\n\
  \  Trace.unbreak               - Remove all breakpoints\n\
  \  Trace.show                  - Show current trace and breakpoints\n\
  \  Trace.reset                 - Reset all tracing and breaking\n\
  \  Print.sgn                   - Print current signature\n\
  \  Print.prog                  - Print current signature as program\n\
  \  Print.subord                - Print current subordination relation\n\
  \  Print.domains               - Print registered constraint domains\n\
  \  Print.TeX.sgn               - Print signature in TeX format\n\
  \  Print.TeX.prog              - Print signature in TeX format as program\n\
  \  Timers.show                 - Print and reset timers\n\
  \  Timers.reset                - Reset timers\n\
  \  Timers.check                - Print, but do not reset timers.\n\
  \  OS.chDir <file>             - Change working directory to <file>\n\
  \  OS.getDir                   - Print current working directory\n\
  \  OS.exit                     - Exit Twelf server\n\
  \  quit                        - Quit Twelf server (same as exit)\n\
  \  Config.read <file>          - Read current configuration from <file>\n\
  \  Config.load                 - Load current configuration\n\
  \  Config.append               - Load current configuration without prior reset\n\
  \  make <file>                 - Read and load configuration from <file>\n\
  \  reset                       - Reset global signature.\n\
  \  loadFile <file>             - Load Twelf file <file>\n\
  \  decl <id>                   - Show constant declaration for <id>\n\
  \  top                         - Enter interactive query loop\n\
  \  Table.top                   - Enter interactive loop for tables queries\n\
  \  version                     - Print Twelf server's version\n\
  \  help                        - Print this help message\n\
  \\n\
  \Parameters:\n\
  \  chatter <nat>               - Level of verbosity (0 = none, 3 = default)\n\
  \  doubleCheck <bool>          - Perform additional internal type-checking\n\
  \  unsafe <bool>               - Allow unsafe operations (%assert)\n\
  \  autoFreeze <bool>           - Freeze families involved in meta-theorems\n\
  \  Print.implicit <bool>       - Print implicit arguments\n\
  \  Print.depth <limit>         - Cut off printing at depth <limit>\n\
  \  Print.length <limit>        - Cut off printing at length <limit>\n\
  \  Print.indent <nat>          - Indent by <nat> spaces\n\
  \  Print.width <nat>           - Line width for formatting\n\
  \  Trace.detail <nat>          - Detail of tracing\n\
  \  Compile.optimize <bool>     - Optimize during translation to clauses\n\
  \  Recon.trace <bool>          - Trace term reconstruction\n\
  \  Recon.traceMode <reconTraceMode> - Term reconstruction tracing mode\n\
  \  Prover.strategy <strategy>  - Prover strategy\n\
  \  Prover.maxSplit <nat>       - Prover splitting depth bound\n\
  \  Prover.maxRecurse <nat>     - Prover recursion depth bound\n\
  \  Table.strategy <tableStrategy>   - Tabling strategy\n\
  \\n\
  \Server types:\n\
  \  file                        - File name, relative to working directory\n\
  \  id                          - A Twelf identifier\n\
  \  bool                        - Either `true' or `false'\n\
  \  nat                         - A natural number (starting at `0')\n\
  \  limit                       - Either `*' (no limit) or a natural number\n\
  \  reconTraceMode              - Either `Progressive' or `Omniscient'\n\
  \  strategy                    - Either `FRS' or `RFS'\n\
  \  tableStrategy               - Either `Variant' or `Subsumption'\n\
  \\n\
  \See http://www.cs.cmu.edu/~twelf/guide-1-4/ for more information,\n\
  \or type M-x twelf-info (C-c C-h) in Emacs.\n\
  \" (* GEN END TAG OUTSIDE LET *)

  (* serve' (command, args) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for one command must be on the same line.
  *)
  fun (* GEN BEGIN FUN FIRST *) serve' ("set", args) =
      (setParm (tokenize args); serve (Twelf.OK)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("get", args) =
      (print (getParm (tokenize args) ^ "\n");
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Style.check", args) = 
      (checkEmpty args; StyleCheck.check (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Print.sgn", args) =
      (checkEmpty args; Twelf.Print.sgn (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Print.prog", args) =
      (checkEmpty args; Twelf.Print.prog (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Print.subord", args) =
      (checkEmpty args; Twelf.Print.subord (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Print.domains", args) =
      (checkEmpty args; Twelf.Print.domains (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Print.TeX.sgn", args) =
      (checkEmpty args; Twelf.Print.TeX.sgn (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Print.TeX.prog", args) =
      (checkEmpty args; Twelf.Print.TeX.prog (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    (*
      serve' ("toc", args) = error "NYI"
    | serve' ("list-program", args) = error "NYI"
    | serve' ("list-signature", args) = error "NYI"
    *)
    (* | serve' ("type-at", args) = error "NYI" *)
    (* | serve' ("complete-at", args) = error "NYI" *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.trace", args) =
      (Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.traceAll", args) =
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.All);
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.untrace", args) =
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.None);
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.break", args) =
      (Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.breakAll", args) =
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.All);
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.unbreak", args) =
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.None);
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.show", args) =
      (checkEmpty args; Twelf.Trace.show ();
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Trace.reset", args) =
      (checkEmpty args; Twelf.Trace.reset ();
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("Timers.show", args) =
      (checkEmpty args; Timers.show (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Timers.reset", args) =
      (checkEmpty args; Timers.reset (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Timers.check", args) =
      (checkEmpty args; Timers.reset (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("OS.chDir", args) =
      (Twelf.OS.chDir (getFile' args); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("OS.getDir", args) =
      (checkEmpty args; print (Twelf.OS.getDir () ^ "\n"); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("OS.exit", args) =
      (checkEmpty args; ()) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("quit", args) = () (* GEN END FUN BRANCH *)		(* quit, as a concession *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("Config.read", args) =
      let
    	(* GEN BEGIN TAG OUTSIDE LET *) val fileName = getFile (args, "sources.cfg") (* GEN END TAG OUTSIDE LET *)
      in
    	globalConfig := SOME (Twelf.Config.read fileName);
    	serve (Twelf.OK)
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Config.load", args) =
      (case !globalConfig
    	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.load (valOf (!globalConfig)))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("Config.append", args) =
      (case !globalConfig
    	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.append (valOf (!globalConfig)))) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("make", args) =
      let
    	(* GEN BEGIN TAG OUTSIDE LET *) val fileName = getFile (args, "sources.cfg") (* GEN END TAG OUTSIDE LET *)
      in
    	globalConfig := SOME (Twelf.Config.read fileName);
    	serve (Twelf.Config.load (valOf (!globalConfig)))
      end (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("reset", args) =
      (checkEmpty args; Twelf.reset (); serve (Twelf.OK)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("loadFile", args) =
        serve (Twelf.loadFile (getFile' args)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("readDecl", args) =
      (checkEmpty args; serve (Twelf.readDecl ())) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) serve' ("decl", args) =
        serve (Twelf.decl (getId (tokenize args))) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("top", args) =
      (checkEmpty args;
       Twelf.top ();
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("Table.top", args) =
      (checkEmpty args;
       Twelf.Table.top ();
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("version", args) =
      (print (Twelf.version ^ "\n");
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' ("help", args) =
      (print (helpString);
       serve (Twelf.OK)) (* GEN END FUN BRANCH *)

    | (* GEN BEGIN FUN BRANCH *) serve' (t, args) =
         error ("Unrecognized command " ^ quote t) (* GEN END FUN BRANCH *)

  and serveLine () = serve' (readLine ())

  and (* GEN BEGIN FUN FIRST *) serve (Twelf.OK) = (issue (Twelf.OK); serveLine ()) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) serve (Twelf.ABORT) = (issue (Twelf.ABORT); serveLine ()) (* GEN END FUN BRANCH *)

  fun serveTop (status) =
      serve (status)
      handle Error (msg) => (print ("Server error: " ^ msg ^ "\n");
  			     serveTop (Twelf.ABORT))
  	   | exn => (print ("Uncaught exception: " ^ exnMessage exn ^ "\n");
  		     serveTop (Twelf.ABORT))

  fun server (name, _) =
      (* ignore server name and arguments *)
      (print (Twelf.version ^ "\n");
       Timing.init ();			(* initialize timers *)
       SigINT.interruptLoop ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => serveTop (Twelf.OK) (* GEN END FUNCTION EXPRESSION *));
       OS.Process.success)

end (* GEN END FUNCTOR DECL *);  (* functor Server *)

structure Server =
  Server (structure SigINT = SigINT
	  structure Timing = Timing
	  structure Lexer = Lexer
	  structure Twelf = Twelf);
