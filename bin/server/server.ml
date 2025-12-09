module type SERVER =
sig

  let server : string * string list -> OS.Process.status

end  (* module type SERVER *)

module Server
  (SigINT : SIGINT)
   (Timing : TIMING)
   (Lexer : LEXER)
   (Twelf : TWELF)
  :> SERVER =
struct

  let globalConfig : Twelf.Config.config option ref = ref NONE

  (* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)
  let rec readLine () =
      let
        (* let line = TextIO.inputLine (TextIO.stdIn) *)
	(* Fix for MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *)
	let rec getLine () = Compat.inputLine97 (TextIO.stdIn)
	                 handle OS.SysErr (_, SOME _) => getLine ()
	let line = getLine ()
        let rec triml ss = Substring.dropl Char.isSpace ss
        let rec trimr ss = Substring.dropr Char.isSpace ss
        let line' = triml (trimr (Compat.Substring.full line))
      in
	if line = ""
	  then ("OS.exit", "")
	else if Substring.size (line') = 0
	  then readLine ()
        else
          let
            let (command', args') = Substring.position " " line'
          in
            (Substring.string command',
             Substring.string (triml args'))
	  end
      end
  
  (* tokenize (args) = [token1, token2, ..., tokenn]
     splits the arguments string into a list of space-separated
     tokens
  *)
  let rec tokenize (args) = String.tokens Char.isSpace args

  (* exception Error for server errors *)
  exception Error of string
  let rec error (msg) = raise Error(msg)

  let rec quote (string) = "`" ^ string ^ "'"

  (* Print the OK or ABORT messages which are parsed by Emacs *)
  let rec issue = function (Twelf.OK) -> print ("%% OK %%\n")
    | (Twelf.ABORT) -> print ("%% ABORT %%\n")

  (* Checking if there are no extraneous arguments *)
  let rec checkEmpty = function ("") -> ()
    | (args) -> error "Extraneous arguments"

  (* Command argument types *)
  (* File names, given a default *)
  let rec getFile = function ("", default) -> default
    | (fileName, default) -> fileName

  (* File names, not defaults *)
  let rec getFile' = function ("") -> error "Missing filename"
    | (fileName) -> fileName

  (* Identifiers, used as a constant *)
  let rec getId = function (id::nil) -> id
    | (nil) -> error "Missing identifier"
    | (ts) -> error "Extraneous arguments"

  (* Identifiers, used as a trace specification *)
  let rec getIds (ids) = ids

  (* Strategies for %prove, %establish *)
  let rec getStrategy = function ("FRS"::nil) -> Twelf.Prover.FRS
    | ("RFS"::nil) -> Twelf.Prover.RFS
    | (nil) -> error "Missing strategy"
    | (t::nil) -> error (quote t ^ " is not a strategy (must be FRS or RFS)")
    | (ts) -> error "Extraneous arguments"

  let rec strategyToString = function (Twelf.Prover.FRS) -> "FRS"
    | (Twelf.Prover.RFS) -> "RFS"

  (* Booleans *)
  let rec getBool = function ("true"::nil) -> true
    | ("false"::nil) -> false
    | (nil) -> error "Missing boolean value"
    | (t::nil) -> error (quote t ^ " is not a boolean")
    | (ts) -> error "Extraneous arguments"

  (* Natural numbers *)
  let rec getNat (t::nil) =
        (Lexer.stringToNat t
	 handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number"))
    | getNat (nil) = error "Missing natural number"
    | getNat (ts) = error "Extraneous arguments"

  (* Limits ( *, or natural number) *)
  let rec getLimit = function ("*"::nil) -> NONE
    | (t::ts) -> SOME (getNat (t::ts))
    | (nil) -> error "Missing `*' or natural number"

  let rec limitToString = function (NONE) -> "*"
    | (SOME(i)) -> Int.toString i

  (* Tabling strategy *)
  let rec getTableStrategy = function ("Variant"::nil) -> Twelf.Table.Variant
    | ("Subsumption"::nil) -> Twelf.Table.Subsumption
    | (nil) -> error "Missing tabling strategy"
    | (t::nil) -> error (quote t ^ " is not a tabling strategy (must be Variant or Subsumption)")
    | (ts) -> error "Extraneous arguments"

  let rec tableStrategyToString = function (Twelf.Table.Variant) -> "Variant"
    | (Twelf.Table.Subsumption) -> "Subsumption"

  (* Tracing mode for term reconstruction *)
  let rec getReconTraceMode = function ("Progressive"::nil) -> Twelf.Recon.Progressive
    | ("Omniscient"::nil) -> Twelf.Recon.Omniscient
    | (nil) -> error "Missing tracing reconstruction mode"
    | (t::nil) -> error (quote t ^ " is not a tracing reconstruction mode\n(must be Progressive or Omniscient)")
    | (ts) -> error "Extraneous arguments"

  let rec reconTraceModeToString = function (Twelf.Recon.Progressive) -> "Progressive"
    | (Twelf.Recon.Omniscient) -> "Omniscient"


  (* Compile options *)
  let rec getCompileOpt = function ("No"::nil) -> Twelf.Compile.No
    | ("LinearHeads"::nil) -> Twelf.Compile.LinearHeads
    | ("Indexing"::nil) -> Twelf.Compile.Indexing
    | (nil) -> error "Missing tabling strategy"
    | (t::nil) -> error (quote t ^ " is not a compile option (must be No, LinearHeads, or Indexing ")
    | (ts) -> error "Extraneous arguments"

  let rec compOptToString = function (Twelf.Compile.No) -> "No"
    | (Twelf.Compile.LinearHeads) -> "LinearHeads"
    | (Twelf.Compile.Indexing) -> "Indexing"

  (* Setting Twelf parameters *)
  let rec setParm = function ("chatter"::ts) -> Twelf.chatter := getNat ts
    | ("doubleCheck"::ts) -> Twelf.doubleCheck := getBool ts
    | ("unsafe"::ts) -> Twelf.unsafe := getBool ts
    | ("autoFreeze"::ts) -> Twelf.autoFreeze := getBool ts
    | ("Print.implicit"::ts) -> Twelf.Print.implicit := getBool ts
    | ("Print.depth"::ts) -> Twelf.Print.depth := getLimit ts
    | ("Print.length"::ts) -> Twelf.Print.length := getLimit ts
    | ("Print.indent"::ts) -> Twelf.Print.indent := getNat ts
    | ("Print.width"::ts) -> Twelf.Print.width := getNat ts
    | ("Trace.detail"::ts) -> Twelf.Trace.detail := getNat ts
    | ("Compile.optimize"::ts) -> Twelf.Compile.optimize := getCompileOpt ts
    | ("Recon.trace"::ts) -> Twelf.Recon.trace := getBool ts
    | ("Recon.traceMode"::ts) -> Twelf.Recon.traceMode := getReconTraceMode ts
    | ("Prover.strategy"::ts) -> Twelf.Prover.strategy := getStrategy ts
    | ("Prover.maxSplit"::ts) -> Twelf.Prover.maxSplit := getNat ts
    | ("Prover.maxRecurse"::ts) -> Twelf.Prover.maxRecurse := getNat ts
    | ("Table.strategy"::ts) -> Twelf.Table.strategy := getTableStrategy ts
    | ("Table.strengthen"::ts) -> Twelf.Table.strengthen := getBool ts
    | (t::ts) -> error ("Unknown parameter " ^ quote t)
    | (nil) -> error ("Missing parameter")

  (* Getting Twelf parameter values *)
  let rec getParm = function ("chatter"::ts) -> Int.toString (!Twelf.chatter)
    | ("doubleCheck"::ts) -> Bool.toString (!Twelf.doubleCheck)
    | ("unsafe"::ts) -> Bool.toString (!Twelf.unsafe)
    | ("autoFreeze"::ts) -> Bool.toString (!Twelf.autoFreeze)
    | ("Print.implicit"::ts) -> Bool.toString (!Twelf.Print.implicit)
    | ("Print.depth"::ts) -> limitToString (!Twelf.Print.depth)
    | ("Print.length"::ts) -> limitToString (!Twelf.Print.length)
    | ("Print.indent"::ts) -> Int.toString (!Twelf.Print.indent)
    | ("Print.width"::ts) -> Int.toString (!Twelf.Print.width)
    | ("Trace.detail"::ts) -> Int.toString (!Twelf.Trace.detail)
    | ("Compile.optimize"::ts) -> compOptToString (!Twelf.Compile.optimize)
    | ("Recon.trace"::ts) -> Bool.toString (!Twelf.Recon.trace)
    | ("Recon.traceMode"::ts) -> reconTraceModeToString (!Twelf.Recon.traceMode)
    | ("Prover.strategy"::ts) -> strategyToString (!Twelf.Prover.strategy)
    | ("Prover.maxSplit"::ts) -> Int.toString (!Twelf.Prover.maxSplit)
    | ("Prover.maxRecurse"::ts) -> Int.toString (!Twelf.Prover.maxRecurse)
   | ("Table.strategy"::ts) -> tableStrategyToString (!Twelf.Table.strategy) 
    | (t::ts) -> error ("Unknown parameter " ^ quote t)
    | (nil) -> error ("Missing parameter")

  (* extracted from doc/guide/twelf.texi *)
  let helpString =
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
\  Print.sgn                   - Print current module type\n\
\  Print.prog                  - Print current module type as program\n\
\  Print.subord                - Print current subordination relation\n\
\  Print.domains               - Print registered constraint domains\n\
\  Print.TeX.sgn               - Print module type in TeX format\n\
\  Print.TeX.prog              - Print module type in TeX format as program\n\
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
\  reset                       - Reset global module type.\n\
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
  let rec serve' = function ("set", args) -> 
      (setParm (tokenize args); serve (Twelf.OK))
    | ("get", args) -> 
      (print (getParm (tokenize args) ^ "\n");
       serve (Twelf.OK))
    | ("Style.check", args) -> 
      (checkEmpty args; StyleCheck.check (); serve (Twelf.OK))
    | ("Print.sgn", args) -> 
      (checkEmpty args; Twelf.Print.sgn (); serve (Twelf.OK))
    | ("Print.prog", args) -> 
      (checkEmpty args; Twelf.Print.prog (); serve (Twelf.OK))
    | ("Print.subord", args) -> 
      (checkEmpty args; Twelf.Print.subord (); serve (Twelf.OK))
    | ("Print.domains", args) -> 
      (checkEmpty args; Twelf.Print.domains (); serve (Twelf.OK))
    | ("Print.TeX.sgn", args) -> 
      (checkEmpty args; Twelf.Print.TeX.sgn (); serve (Twelf.OK))
    | ("Print.TeX.prog", args) -> 
      (checkEmpty args; Twelf.Print.TeX.prog (); serve (Twelf.OK))
    (*
      serve' ("toc", args) = error "NYI"
    | ("list-program", args) -> error "NYI"
    | ("list-module type", args) -> error "NYI"
    *)
    (* | serve' ("type-at", args) = error "NYI" *)
    (* | serve' ("complete-at", args) = error "NYI" *)

    | ("Trace.trace", args) -> 
      (Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK))
    | ("Trace.traceAll", args) -> 
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.All);
       serve (Twelf.OK))
    | ("Trace.untrace", args) -> 
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.None);
       serve (Twelf.OK))

    | ("Trace.break", args) -> 
      (Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK))
    | ("Trace.breakAll", args) -> 
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.All);
       serve (Twelf.OK))
    | ("Trace.unbreak", args) -> 
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.None);
       serve (Twelf.OK))

    | ("Trace.show", args) -> 
      (checkEmpty args; Twelf.Trace.show ();
       serve (Twelf.OK))
    | ("Trace.reset", args) -> 
      (checkEmpty args; Twelf.Trace.reset ();
       serve (Twelf.OK))

    | ("Timers.show", args) -> 
      (checkEmpty args; Timers.show (); serve (Twelf.OK))
    | ("Timers.reset", args) -> 
      (checkEmpty args; Timers.reset (); serve (Twelf.OK))
    | ("Timers.check", args) -> 
      (checkEmpty args; Timers.reset (); serve (Twelf.OK))

    | ("OS.chDir", args) -> 
      (Twelf.OS.chDir (getFile' args); serve (Twelf.OK))
    | ("OS.getDir", args) -> 
      (checkEmpty args; print (Twelf.OS.getDir () ^ "\n"); serve (Twelf.OK))
    | ("OS.exit", args) -> 
      (checkEmpty args; ())

    | ("quit", args) -> ()		(* quit, as a concession *)

    | ("Config.read", args) -> 
      let
	let fileName = getFile (args, "sources.cfg")
      in
	globalConfig := SOME (Twelf.Config.read fileName);
	serve (Twelf.OK)
      end
    | serve' ("Config.load", args) =
      (case !globalConfig
	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.load (valOf (!globalConfig))))
    | serve' ("Config.append", args) =
      (case !globalConfig
	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.append (valOf (!globalConfig))))
    | serve' ("make", args) =
      let
	let fileName = getFile (args, "sources.cfg")
      in
	globalConfig := SOME (Twelf.Config.read fileName);
	serve (Twelf.Config.load (valOf (!globalConfig)))
      end

    | serve' ("reset", args) =
      (checkEmpty args; Twelf.reset (); serve (Twelf.OK))
    | serve' ("loadFile", args) =
        serve (Twelf.loadFile (getFile' args))
    | serve' ("readDecl", args) =
      (checkEmpty args; serve (Twelf.readDecl ()))
    | serve' ("decl", args) =
        serve (Twelf.decl (getId (tokenize args)))

    | serve' ("top", args) =
      (checkEmpty args;
       Twelf.top ();
       serve (Twelf.OK))

    | serve' ("Table.top", args) =
      (checkEmpty args;
       Twelf.Table.top ();
       serve (Twelf.OK))

    | serve' ("version", args) =
      (print (Twelf.version ^ "\n");
       serve (Twelf.OK))

    | serve' ("help", args) =
      (print (helpString);
       serve (Twelf.OK))

    | serve' (t, args) =
         error ("Unrecognized command " ^ quote t)

  and serveLine () = serve' (readLine ())

  and serve (Twelf.OK) = (issue (Twelf.OK); serveLine ())
    | serve (Twelf.ABORT) = (issue (Twelf.ABORT); serveLine ())

  let rec serveTop (status) =
      serve (status)
      handle Error (msg) => (print ("Server error: " ^ msg ^ "\n");
			     serveTop (Twelf.ABORT))
	   | exn => (print ("Uncaught exception: " ^ exnMessage exn ^ "\n");
		     serveTop (Twelf.ABORT))

  let rec server (name, _) =
      (* ignore server name and arguments *)
      (print (Twelf.version ^ "\n");
       Timing.init ();			(* initialize timers *)
       SigINT.interruptLoop (fn () => serveTop (Twelf.OK));
       OS.Process.success)

end;; (* functor Server *)

module Server =
  Server (module SigINT = SigINT
	  module Timing = Timing
	  module Lexer = Lexer
	  module Twelf = Twelf);
