signature SERVER =
sig

  val server : string * string list -> OS.Process.status

end  (* signature SERVER *)

functor Server
  (structure SigINT : SIGINT
   structure Timing : TIMING
   structure Lexer : LEXER
   structure Twelf : TWELF)
  :> SERVER =
struct

  val globalConfig : Twelf.Config.config option ref = ref NONE

  (* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)
  fun readLine () =
      let
        (* val line = TextIO.inputLine (TextIO.stdIn) *)
  	(* Fix for MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *)
  	fun getLine () = Compat.inputLine97 (TextIO.stdIn)
  	                 handle OS.SysErr (_, SOME _) => getLine ()
  	val line = getLine ()
        fun triml ss = Substring.dropl Char.isSpace ss
        fun trimr ss = Substring.dropr Char.isSpace ss
        val line' = triml (trimr (Compat.Substring.full line))
      in
  	if line = ""
  	  then ("OS.exit", "")
  	else if Substring.size (line') = 0
  	  then readLine ()
        else
          let
            val (command', args') = Substring.position " " line'
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
  fun issue (Twelf.OK) = print ("%% OK %%\n")
    | (* GEN CASE BRANCH *) issue (Twelf.ABORT) = print ("%% ABORT %%\n")

  (* Checking if there are no extraneous arguments *)
  fun checkEmpty ("") = ()
    | (* GEN CASE BRANCH *) checkEmpty (args) = error "Extraneous arguments"

  (* Command argument types *)
  (* File names, given a default *)
  fun getFile ("", default) = default
    | (* GEN CASE BRANCH *) getFile (fileName, default) = fileName

  (* File names, not defaults *)
  fun getFile' ("") = error "Missing filename"
    | (* GEN CASE BRANCH *) getFile' (fileName) = fileName

  (* Identifiers, used as a constant *)
  fun getId (id::nil) = id
    | (* GEN CASE BRANCH *) getId (nil) = error "Missing identifier"
    | (* GEN CASE BRANCH *) getId (ts) = error "Extraneous arguments"

  (* Identifiers, used as a trace specification *)
  fun getIds (ids) = ids

  (* Strategies for %prove, %establish *)
  fun getStrategy ("FRS"::nil) = Twelf.Prover.FRS
    | (* GEN CASE BRANCH *) getStrategy ("RFS"::nil) = Twelf.Prover.RFS
    | (* GEN CASE BRANCH *) getStrategy (nil) = error "Missing strategy"
    | (* GEN CASE BRANCH *) getStrategy (t::nil) = error (quote t ^ " is not a strategy (must be FRS or RFS)")
    | (* GEN CASE BRANCH *) getStrategy (ts) = error "Extraneous arguments"

  fun strategyToString (Twelf.Prover.FRS) = "FRS"
    | (* GEN CASE BRANCH *) strategyToString (Twelf.Prover.RFS) = "RFS"

  (* Booleans *)
  fun getBool ("true"::nil) = true
    | (* GEN CASE BRANCH *) getBool ("false"::nil) = false
    | (* GEN CASE BRANCH *) getBool (nil) = error "Missing boolean value"
    | (* GEN CASE BRANCH *) getBool (t::nil) = error (quote t ^ " is not a boolean")
    | (* GEN CASE BRANCH *) getBool (ts) = error "Extraneous arguments"

  (* Natural numbers *)
  fun getNat (t::nil) =
        (Lexer.stringToNat t
  	 handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number"))
    | (* GEN CASE BRANCH *) getNat (nil) = error "Missing natural number"
    | (* GEN CASE BRANCH *) getNat (ts) = error "Extraneous arguments"

  (* Limits ( *, or natural number) *)
  fun getLimit ("*"::nil) = NONE
    | (* GEN CASE BRANCH *) getLimit (t::ts) = SOME (getNat (t::ts))
    | (* GEN CASE BRANCH *) getLimit (nil) = error "Missing `*' or natural number"

  fun limitToString (NONE) = "*"
    | (* GEN CASE BRANCH *) limitToString (SOME(i)) = Int.toString i

  (* Tabling strategy *)
  fun getTableStrategy ("Variant"::nil) = Twelf.Table.Variant
    | (* GEN CASE BRANCH *) getTableStrategy ("Subsumption"::nil) = Twelf.Table.Subsumption
    | (* GEN CASE BRANCH *) getTableStrategy (nil) = error "Missing tabling strategy"
    | (* GEN CASE BRANCH *) getTableStrategy (t::nil) = error (quote t ^ " is not a tabling strategy (must be Variant or Subsumption)")
    | (* GEN CASE BRANCH *) getTableStrategy (ts) = error "Extraneous arguments"

  fun tableStrategyToString (Twelf.Table.Variant) = "Variant"
    | (* GEN CASE BRANCH *) tableStrategyToString (Twelf.Table.Subsumption) = "Subsumption"

  (* Tracing mode for term reconstruction *)
  fun getReconTraceMode ("Progressive"::nil) = Twelf.Recon.Progressive
    | (* GEN CASE BRANCH *) getReconTraceMode ("Omniscient"::nil) = Twelf.Recon.Omniscient
    | (* GEN CASE BRANCH *) getReconTraceMode (nil) = error "Missing tracing reconstruction mode"
    | (* GEN CASE BRANCH *) getReconTraceMode (t::nil) = error (quote t ^ " is not a tracing reconstruction mode\n(must be Progressive or Omniscient)")
    | (* GEN CASE BRANCH *) getReconTraceMode (ts) = error "Extraneous arguments"

  fun reconTraceModeToString (Twelf.Recon.Progressive) = "Progressive"
    | (* GEN CASE BRANCH *) reconTraceModeToString (Twelf.Recon.Omniscient) = "Omniscient"


  (* Compile options *)
  fun getCompileOpt ("No"::nil) = Twelf.Compile.No
    | (* GEN CASE BRANCH *) getCompileOpt ("LinearHeads"::nil) = Twelf.Compile.LinearHeads
    | (* GEN CASE BRANCH *) getCompileOpt ("Indexing"::nil) = Twelf.Compile.Indexing
    | (* GEN CASE BRANCH *) getCompileOpt (nil) = error "Missing tabling strategy"
    | (* GEN CASE BRANCH *) getCompileOpt (t::nil) = error (quote t ^ " is not a compile option (must be No, LinearHeads, or Indexing ")
    | (* GEN CASE BRANCH *) getCompileOpt (ts) = error "Extraneous arguments"

  fun compOptToString (Twelf.Compile.No) = "No"
    | (* GEN CASE BRANCH *) compOptToString (Twelf.Compile.LinearHeads) = "LinearHeads"
    | (* GEN CASE BRANCH *) compOptToString (Twelf.Compile.Indexing) = "Indexing"

  (* Setting Twelf parameters *)
  fun setParm ("chatter"::ts) = Twelf.chatter := getNat ts
    | (* GEN CASE BRANCH *) setParm ("doubleCheck"::ts) = Twelf.doubleCheck := getBool ts
    | (* GEN CASE BRANCH *) setParm ("unsafe"::ts) = Twelf.unsafe := getBool ts
    | (* GEN CASE BRANCH *) setParm ("autoFreeze"::ts) = Twelf.autoFreeze := getBool ts
    | (* GEN CASE BRANCH *) setParm ("Print.implicit"::ts) = Twelf.Print.implicit := getBool ts
    | (* GEN CASE BRANCH *) setParm ("Print.depth"::ts) = Twelf.Print.depth := getLimit ts
    | (* GEN CASE BRANCH *) setParm ("Print.length"::ts) = Twelf.Print.length := getLimit ts
    | (* GEN CASE BRANCH *) setParm ("Print.indent"::ts) = Twelf.Print.indent := getNat ts
    | (* GEN CASE BRANCH *) setParm ("Print.width"::ts) = Twelf.Print.width := getNat ts
    | (* GEN CASE BRANCH *) setParm ("Trace.detail"::ts) = Twelf.Trace.detail := getNat ts
    | (* GEN CASE BRANCH *) setParm ("Compile.optimize"::ts) = Twelf.Compile.optimize := getCompileOpt ts
    | (* GEN CASE BRANCH *) setParm ("Recon.trace"::ts) = Twelf.Recon.trace := getBool ts
    | (* GEN CASE BRANCH *) setParm ("Recon.traceMode"::ts) = Twelf.Recon.traceMode := getReconTraceMode ts
    | (* GEN CASE BRANCH *) setParm ("Prover.strategy"::ts) = Twelf.Prover.strategy := getStrategy ts
    | (* GEN CASE BRANCH *) setParm ("Prover.maxSplit"::ts) = Twelf.Prover.maxSplit := getNat ts
    | (* GEN CASE BRANCH *) setParm ("Prover.maxRecurse"::ts) = Twelf.Prover.maxRecurse := getNat ts
    | (* GEN CASE BRANCH *) setParm ("Table.strategy"::ts) = Twelf.Table.strategy := getTableStrategy ts
    | (* GEN CASE BRANCH *) setParm ("Table.strengthen"::ts) = Twelf.Table.strengthen := getBool ts
    | (* GEN CASE BRANCH *) setParm (t::ts) = error ("Unknown parameter " ^ quote t)
    | (* GEN CASE BRANCH *) setParm (nil) = error ("Missing parameter")

  (* Getting Twelf parameter values *)
  fun getParm ("chatter"::ts) = Int.toString (!Twelf.chatter)
    | (* GEN CASE BRANCH *) getParm ("doubleCheck"::ts) = Bool.toString (!Twelf.doubleCheck)
    | (* GEN CASE BRANCH *) getParm ("unsafe"::ts) = Bool.toString (!Twelf.unsafe)
    | (* GEN CASE BRANCH *) getParm ("autoFreeze"::ts) = Bool.toString (!Twelf.autoFreeze)
    | (* GEN CASE BRANCH *) getParm ("Print.implicit"::ts) = Bool.toString (!Twelf.Print.implicit)
    | (* GEN CASE BRANCH *) getParm ("Print.depth"::ts) = limitToString (!Twelf.Print.depth)
    | (* GEN CASE BRANCH *) getParm ("Print.length"::ts) = limitToString (!Twelf.Print.length)
    | (* GEN CASE BRANCH *) getParm ("Print.indent"::ts) = Int.toString (!Twelf.Print.indent)
    | (* GEN CASE BRANCH *) getParm ("Print.width"::ts) = Int.toString (!Twelf.Print.width)
    | (* GEN CASE BRANCH *) getParm ("Trace.detail"::ts) = Int.toString (!Twelf.Trace.detail)
    | (* GEN CASE BRANCH *) getParm ("Compile.optimize"::ts) = compOptToString (!Twelf.Compile.optimize)
    | (* GEN CASE BRANCH *) getParm ("Recon.trace"::ts) = Bool.toString (!Twelf.Recon.trace)
    | (* GEN CASE BRANCH *) getParm ("Recon.traceMode"::ts) = reconTraceModeToString (!Twelf.Recon.traceMode)
    | (* GEN CASE BRANCH *) getParm ("Prover.strategy"::ts) = strategyToString (!Twelf.Prover.strategy)
    | (* GEN CASE BRANCH *) getParm ("Prover.maxSplit"::ts) = Int.toString (!Twelf.Prover.maxSplit)
    | (* GEN CASE BRANCH *) getParm ("Prover.maxRecurse"::ts) = Int.toString (!Twelf.Prover.maxRecurse)
   | (* GEN CASE BRANCH *) getParm ("Table.strategy"::ts) = tableStrategyToString (!Twelf.Table.strategy) 
    | (* GEN CASE BRANCH *) getParm (t::ts) = error ("Unknown parameter " ^ quote t)
    | (* GEN CASE BRANCH *) getParm (nil) = error ("Missing parameter")

  (* extracted from doc/guide/twelf.texi *)
  val helpString =
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
\"

  (* serve' (command, args) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for one command must be on the same line.
  *)
  fun serve' ("set", args) =
      (setParm (tokenize args); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("get", args) =
      (print (getParm (tokenize args) ^ "\n");
       serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Style.check", args) = 
      (checkEmpty args; StyleCheck.check (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Print.sgn", args) =
      (checkEmpty args; Twelf.Print.sgn (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Print.prog", args) =
      (checkEmpty args; Twelf.Print.prog (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Print.subord", args) =
      (checkEmpty args; Twelf.Print.subord (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Print.domains", args) =
      (checkEmpty args; Twelf.Print.domains (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Print.TeX.sgn", args) =
      (checkEmpty args; Twelf.Print.TeX.sgn (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Print.TeX.prog", args) =
      (checkEmpty args; Twelf.Print.TeX.prog (); serve (Twelf.OK))
    (*
      serve' ("toc", args) = error "NYI"
    | serve' ("list-program", args) = error "NYI"
    | serve' ("list-signature", args) = error "NYI"
    *)
    (* | serve' ("type-at", args) = error "NYI" *)
    (* | serve' ("complete-at", args) = error "NYI" *)

    | (* GEN CASE BRANCH *) serve' ("Trace.trace", args) =
      (Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Trace.traceAll", args) =
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.All);
       serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Trace.untrace", args) =
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.None);
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("Trace.break", args) =
      (Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Trace.breakAll", args) =
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.All);
       serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Trace.unbreak", args) =
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.None);
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("Trace.show", args) =
      (checkEmpty args; Twelf.Trace.show ();
       serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Trace.reset", args) =
      (checkEmpty args; Twelf.Trace.reset ();
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("Timers.show", args) =
      (checkEmpty args; Timers.show (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Timers.reset", args) =
      (checkEmpty args; Timers.reset (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("Timers.check", args) =
      (checkEmpty args; Timers.reset (); serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("OS.chDir", args) =
      (Twelf.OS.chDir (getFile' args); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("OS.getDir", args) =
      (checkEmpty args; print (Twelf.OS.getDir () ^ "\n"); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("OS.exit", args) =
      (checkEmpty args; ())

    | (* GEN CASE BRANCH *) serve' ("quit", args) = ()		(* quit, as a concession *)

    | (* GEN CASE BRANCH *) serve' ("Config.read", args) =
      let
    	val fileName = getFile (args, "sources.cfg")
      in
    	globalConfig := SOME (Twelf.Config.read fileName);
    	serve (Twelf.OK)
      end
    | (* GEN CASE BRANCH *) serve' ("Config.load", args) =
      (case !globalConfig
    	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.load (valOf (!globalConfig))))
    | (* GEN CASE BRANCH *) serve' ("Config.append", args) =
      (case !globalConfig
    	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.append (valOf (!globalConfig))))
    | (* GEN CASE BRANCH *) serve' ("make", args) =
      let
    	val fileName = getFile (args, "sources.cfg")
      in
    	globalConfig := SOME (Twelf.Config.read fileName);
    	serve (Twelf.Config.load (valOf (!globalConfig)))
      end

    | (* GEN CASE BRANCH *) serve' ("reset", args) =
      (checkEmpty args; Twelf.reset (); serve (Twelf.OK))
    | (* GEN CASE BRANCH *) serve' ("loadFile", args) =
        serve (Twelf.loadFile (getFile' args))
    | (* GEN CASE BRANCH *) serve' ("readDecl", args) =
      (checkEmpty args; serve (Twelf.readDecl ()))
    | (* GEN CASE BRANCH *) serve' ("decl", args) =
        serve (Twelf.decl (getId (tokenize args)))

    | (* GEN CASE BRANCH *) serve' ("top", args) =
      (checkEmpty args;
       Twelf.top ();
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("Table.top", args) =
      (checkEmpty args;
       Twelf.Table.top ();
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("version", args) =
      (print (Twelf.version ^ "\n");
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' ("help", args) =
      (print (helpString);
       serve (Twelf.OK))

    | (* GEN CASE BRANCH *) serve' (t, args) =
         error ("Unrecognized command " ^ quote t)

  and serveLine () = serve' (readLine ())

  and serve (Twelf.OK) = (issue (Twelf.OK); serveLine ())
    | (* GEN CASE BRANCH *) serve (Twelf.ABORT) = (issue (Twelf.ABORT); serveLine ())

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
       SigINT.interruptLoop (fn () => serveTop (Twelf.OK));
       OS.Process.success)

end;  (* functor Server *)

structure Server =
  Server (structure SigINT = SigINT
	  structure Timing = Timing
	  structure Lexer = Lexer
	  structure Twelf = Twelf);
