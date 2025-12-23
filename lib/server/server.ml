module type SERVER = sig
  val server : string * string list -> OS.Process.status

end

(* signature SERVER *)


module Server (SigINT : Sigint.SIGINT) (Timing : Timing.TIMING) (Lexer : Lexer.LEXER) (Twelf : Twelf.TWELF) : SERVER = struct let globalConfig : Twelf.Config.config option ref = ref None
(* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)

let rec readLine ()  = ( (* val line = TextIO.inputLine (TextIO.stdIn) *)
(* Fix for_sml MLton, Fri Dec 20 21:50:22 2002 -sweeks (fp) *)
let rec getLine ()  = try Compat.inputLine97 (TextIO.stdIn) with OS.SysErr (_, Some _) -> getLine () in let line = getLine () in let rec triml ss  = Substring.dropl Char.isSpace ss in let rec trimr ss  = Substring.dropr Char.isSpace ss in let line' = triml (trimr (Compat.Substring.full line)) in  if line = "" then ("OS.exit", "") else if Substring.size (line') = 0 then readLine () else ( let (command', args') = Substring.position " " line' in  (Substring.string command', Substring.string (triml args')) ) )
(* tokenize (args) = [token1, token2, ..., tokenn]
     splits the arguments string into a list of space-separated
     tokens
  *)

let rec tokenize (args)  = String.tokens Char.isSpace args
(* exception Error for_sml server errors *)

exception Error of string
let rec error (msg)  = raise (Error (msg))
let rec quote (string)  = "`" ^ string ^ "'"
(* Print the OK or ABORT messages which are parsed by Emacs *)

let rec issue = function (Twelf.OK) -> print ("%% OK %%\n") | (Twelf.ABORT) -> print ("%% ABORT %%\n")
(* Checking if there are no extraneous arguments *)

let rec checkEmpty = function ("") -> () | (args) -> error "Extraneous arguments"
(* Command argument types *)

(* File names, given a default *)

let rec getFile = function ("", default) -> default | (fileName, default) -> fileName
(* File names, not defaults *)

let rec getFile' = function ("") -> error "Missing filename" | (fileName) -> fileName
(* Identifiers, a constant *)

let rec getId = function (id :: []) -> id | ([]) -> error "Missing identifier" | (ts) -> error "Extraneous arguments"
(* Identifiers, a trace specification *)

let rec getIds (ids)  = ids
(* Strategies for_sml %prove, %establish *)

let rec getStrategy = function ("FRS" :: []) -> Twelf.Prover.FRS | ("RFS" :: []) -> Twelf.Prover.RFS | ([]) -> error "Missing strategy" | (t :: []) -> error (quote t ^ " is not a strategy (must be FRS or RFS)") | (ts) -> error "Extraneous arguments"
let rec strategyToString = function (Twelf.Prover.FRS) -> "FRS" | (Twelf.Prover.RFS) -> "RFS"
(* Booleans *)

let rec getBool = function ("true" :: []) -> true | ("false" :: []) -> false | ([]) -> error "Missing boolean value" | (t :: []) -> error (quote t ^ " is not a boolean") | (ts) -> error "Extraneous arguments"
(* Natural numbers *)

let rec getNat = function (t :: []) -> (try Lexer.stringToNat t with Lexer.NotDigit (char) -> error (quote t ^ " is not a natural number")) | ([]) -> error "Missing natural number" | (ts) -> error "Extraneous arguments"
(* Limits ( *, or natural number) *)

let rec getLimit = function ("*" :: []) -> None | (t :: ts) -> Some (getNat (t :: ts)) | ([]) -> error "Missing `*' or natural number"
let rec limitToString = function (None) -> "*" | (Some (i)) -> Int.toString i
(* Tabling strategy *)

let rec getTableStrategy = function ("Variant" :: []) -> Twelf.Table.Variant | ("Subsumption" :: []) -> Twelf.Table.Subsumption | ([]) -> error "Missing tabling strategy" | (t :: []) -> error (quote t ^ " is not a tabling strategy (must be Variant or Subsumption)") | (ts) -> error "Extraneous arguments"
let rec tableStrategyToString = function (Twelf.Table.Variant) -> "Variant" | (Twelf.Table.Subsumption) -> "Subsumption"
(* Tracing mode for_sml term reconstruction *)

let rec getReconTraceMode = function ("Progressive" :: []) -> Twelf.Recon.Progressive | ("Omniscient" :: []) -> Twelf.Recon.Omniscient | ([]) -> error "Missing tracing reconstruction mode" | (t :: []) -> error (quote t ^ " is not a tracing reconstruction mode\n(must be Progressive or Omniscient)") | (ts) -> error "Extraneous arguments"
let rec reconTraceModeToString = function (Twelf.Recon.Progressive) -> "Progressive" | (Twelf.Recon.Omniscient) -> "Omniscient"
(* Compile options *)

let rec getCompileOpt = function ("No" :: []) -> Twelf.Compile.No | ("LinearHeads" :: []) -> Twelf.Compile.LinearHeads | ("Indexing" :: []) -> Twelf.Compile.Indexing | ([]) -> error "Missing tabling strategy" | (t :: []) -> error (quote t ^ " is not a compile option (must be No, LinearHeads, or Indexing ") | (ts) -> error "Extraneous arguments"
let rec compOptToString = function (Twelf.Compile.No) -> "No" | (Twelf.Compile.LinearHeads) -> "LinearHeads" | (Twelf.Compile.Indexing) -> "Indexing"
(* Setting Twelf parameters *)

let rec setParm = function ("chatter" :: ts) -> Twelf.chatter := getNat ts | ("doubleCheck" :: ts) -> Twelf.doubleCheck := getBool ts | ("unsafe" :: ts) -> Twelf.unsafe := getBool ts | ("autoFreeze" :: ts) -> Twelf.autoFreeze := getBool ts | ("Print.implicit" :: ts) -> Twelf.Print.implicit := getBool ts | ("Print.depth" :: ts) -> Twelf.Print.depth := getLimit ts | ("Print.length" :: ts) -> Twelf.Print.length := getLimit ts | ("Print.indent" :: ts) -> Twelf.Print.indent := getNat ts | ("Print.width" :: ts) -> Twelf.Print.width := getNat ts | ("Trace.detail" :: ts) -> Twelf.Trace.detail := getNat ts | ("Compile.optimize" :: ts) -> Twelf.Compile.optimize := getCompileOpt ts | ("Recon.trace" :: ts) -> Twelf.Recon.trace := getBool ts | ("Recon.traceMode" :: ts) -> Twelf.Recon.traceMode := getReconTraceMode ts | ("Prover.strategy" :: ts) -> Twelf.Prover.strategy := getStrategy ts | ("Prover.maxSplit" :: ts) -> Twelf.Prover.maxSplit := getNat ts | ("Prover.maxRecurse" :: ts) -> Twelf.Prover.maxRecurse := getNat ts | ("Table.strategy" :: ts) -> Twelf.Table.strategy := getTableStrategy ts | ("Table.strengthen" :: ts) -> Twelf.Table.strengthen := getBool ts | (t :: ts) -> error ("Unknown parameter " ^ quote t) | ([]) -> error ("Missing parameter")
(* Getting Twelf parameter values *)

let rec getParm = function ("chatter" :: ts) -> Int.toString (! Twelf.chatter) | ("doubleCheck" :: ts) -> Bool.toString (! Twelf.doubleCheck) | ("unsafe" :: ts) -> Bool.toString (! Twelf.unsafe) | ("autoFreeze" :: ts) -> Bool.toString (! Twelf.autoFreeze) | ("Print.implicit" :: ts) -> Bool.toString (! Twelf.Print.implicit) | ("Print.depth" :: ts) -> limitToString (! Twelf.Print.depth) | ("Print.length" :: ts) -> limitToString (! Twelf.Print.length) | ("Print.indent" :: ts) -> Int.toString (! Twelf.Print.indent) | ("Print.width" :: ts) -> Int.toString (! Twelf.Print.width) | ("Trace.detail" :: ts) -> Int.toString (! Twelf.Trace.detail) | ("Compile.optimize" :: ts) -> compOptToString (! Twelf.Compile.optimize) | ("Recon.trace" :: ts) -> Bool.toString (! Twelf.Recon.trace) | ("Recon.traceMode" :: ts) -> reconTraceModeToString (! Twelf.Recon.traceMode) | ("Prover.strategy" :: ts) -> strategyToString (! Twelf.Prover.strategy) | ("Prover.maxSplit" :: ts) -> Int.toString (! Twelf.Prover.maxSplit) | ("Prover.maxRecurse" :: ts) -> Int.toString (! Twelf.Prover.maxRecurse) | ("Table.strategy" :: ts) -> tableStrategyToString (! Twelf.Table.strategy) | (t :: ts) -> error ("Unknown parameter " ^ quote t) | ([]) -> error ("Missing parameter")
(* extracted from doc/guide/twelf.texi *)

let helpString = {|Commands:
  set <parameter> <value>     - Set <parameter> to <value>
  get <parameter>             - Print the current value of <parameter>
  Trace.trace <id1> ... <idn> - Trace given constants
  Trace.traceAll              - Trace all constants
  Trace.untrace               - Untrace all constants
  Trace.break <id1> ... <idn> - Set breakpoint for_sml given constants
 Trace.breakAll              - Break on all constants
 Trace.unbreak               - Remove all breakpoints
 Trace.show                  - Show current trace and breakpoints
 Trace.reset                 - Reset all tracing and breaking
 Print.sgn                   - Print current signature
 Print.prog                  - Print current program
 Print.subord                - Print current subordination relation
  Print.domains               - Print registered constraint domains
  Print.TeX.sgn               - Print signature in TeX format
  Print.TeX.prog              - Print signature in TeX program
  Timers.show                 - Print and reset timers
  Timers.reset                - Reset timers
  Timers.check                - Print, but do not reset timers.
  OS.chDir <file>             - Change working directory to <file>
  OS.getDir                   - Print current working directory
  OS.exit                     - Exit Twelf server
  quit                        - Quit Twelf server (exit)
  Config.read <file>          - Read current configuration from <file>
  Config.load                 - Load current configuration
  Config.append               - Load current configuration without prior reset
  make <file>                 - Read and load configuration from <file>
  reset                       - Reset global signature.
  loadFile <file>             - Load Twelf file <file>
  decl <id>                   - Show constant declaration for_sml <id>
  top                         - Enter interactive query loop
  Table.top                   - Enter interactive loop for_sml tables queries
  version                     - Print Twelf server's version
  help                        - Print this help message

Parameters:
  chatter <nat>               - Level of verbosity (0 = none, 3 = default)
  doubleCheck <bool>          - Perform additional internal type-checking
  unsafe <bool>               - Allow unsafe operations (%assert)
  autoFreeze <bool>           - Freeze families involved in meta-theorems
  Print.implicit <bool>       - Print implicit arguments
  Print.depth <limit>         - Cut off printing at depth <limit>
  Print.length <limit>        - Cut off printing at length <limit>
  Print.indent <nat>          - Indent by <nat> spaces
  Print.width <nat>           - Line width for_sml formatting
  Trace.detail <nat>          - Detail of tracing
  Compile.optimize <bool>     - Optimize during translation to clauses
  Recon.trace <bool>          - Trace term reconstruction
  Recon.traceMode <reconTraceMode> - Term reconstruction tracing mode
  Prover.strategy <strategy>  - Prover strategy
  Prover.maxSplit <nat>       - Prover splitting depth bound
  Prover.maxRecurse <nat>     - Prover recursion depth bound
  Table.strategy <tableStrategy>   - Tabling strategy

Server types:
  file                        - File name, relative to working directory
  id                          - A Twelf identifier
  bool                        - Either `true' or `false'
  nat                         - A natural number (starting at `0')
  limit                       - Either `*' (no limit) or a natural number
  reconTraceMode              - Either `Progressive' or `Omniscient'
  strategy                    - Either `FRS' or `RFS'
  tableStrategy               - Either `Variant' or `Subsumption'

See http://www.cs.cmu.edu/~twelf/guide-1-4/ for_sml more information,
or type M-x twelf-info (C-c C-h) in Emacs.
|}
(* serve' (command, args) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for_sml one command must be on the same line.
  *)

let rec serve' = function ("set", args) -> (setParm (tokenize args); serve (Twelf.OK)) | ("get", args) -> (print (getParm (tokenize args) ^ "\n"); serve (Twelf.OK)) | ("Style.check", args) -> (checkEmpty args; StyleCheck.check (); serve (Twelf.OK)) | ("Print.sgn", args) -> (checkEmpty args; Twelf.Print.sgn (); serve (Twelf.OK)) | ("Print.prog", args) -> (checkEmpty args; Twelf.Print.prog (); serve (Twelf.OK)) | ("Print.subord", args) -> (checkEmpty args; Twelf.Print.subord (); serve (Twelf.OK)) | ("Print.domains", args) -> (checkEmpty args; Twelf.Print.domains (); serve (Twelf.OK)) | ("Print.TeX.sgn", args) -> (checkEmpty args; Twelf.Print.TeX.sgn (); serve (Twelf.OK)) | ("Print.TeX.prog", args) -> (checkEmpty args; Twelf.Print.TeX.prog (); serve (Twelf.OK)) | ("Trace.trace", args) -> (Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args))); serve (Twelf.OK)) | ("Trace.traceAll", args) -> (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.All); serve (Twelf.OK)) | ("Trace.untrace", args) -> (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.None); serve (Twelf.OK)) | ("Trace.break", args) -> (Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args))); serve (Twelf.OK)) | ("Trace.breakAll", args) -> (checkEmpty args; Twelf.Trace.break (Twelf.Trace.All); serve (Twelf.OK)) | ("Trace.unbreak", args) -> (checkEmpty args; Twelf.Trace.break (Twelf.Trace.None); serve (Twelf.OK)) | ("Trace.show", args) -> (checkEmpty args; Twelf.Trace.show (); serve (Twelf.OK)) | ("Trace.reset", args) -> (checkEmpty args; Twelf.Trace.reset (); serve (Twelf.OK)) | ("Timers.show", args) -> (checkEmpty args; Timers.show (); serve (Twelf.OK)) | ("Timers.reset", args) -> (checkEmpty args; Timers.reset (); serve (Twelf.OK)) | ("Timers.check", args) -> (checkEmpty args; Timers.reset (); serve (Twelf.OK)) | ("OS.chDir", args) -> (Twelf.OS.chDir (getFile' args); serve (Twelf.OK)) | ("OS.getDir", args) -> (checkEmpty args; print (Twelf.OS.getDir () ^ "\n"); serve (Twelf.OK)) | ("OS.exit", args) -> (checkEmpty args; ()) | ("quit", args) -> () | ("Config.read", args) -> ( let fileName = getFile (args, "sources.cfg") in  globalConfig := Some (Twelf.Config.read fileName); serve (Twelf.OK) ) | ("Config.load", args) -> (match ! globalConfig with None -> (globalConfig := Some (Twelf.Config.read "sources.cfg")) | _ -> (); serve (Twelf.Config.load (valOf (! globalConfig)))) | ("Config.append", args) -> (match ! globalConfig with None -> (globalConfig := Some (Twelf.Config.read "sources.cfg")) | _ -> (); serve (Twelf.Config.append (valOf (! globalConfig)))) | ("make", args) -> ( let fileName = getFile (args, "sources.cfg") in  globalConfig := Some (Twelf.Config.read fileName); serve (Twelf.Config.load (valOf (! globalConfig))) ) | ("reset", args) -> (checkEmpty args; Twelf.reset (); serve (Twelf.OK)) | ("loadFile", args) -> serve (Twelf.loadFile (getFile' args)) | ("readDecl", args) -> (checkEmpty args; serve (Twelf.readDecl ())) | ("decl", args) -> serve (Twelf.decl (getId (tokenize args))) | ("top", args) -> (checkEmpty args; Twelf.top (); serve (Twelf.OK)) | ("Table.top", args) -> (checkEmpty args; Twelf.Table.top (); serve (Twelf.OK)) | ("version", args) -> (print (Twelf.version ^ "\n"); serve (Twelf.OK)) | ("help", args) -> (print (helpString); serve (Twelf.OK)) | (t, args) -> error ("Unrecognized command " ^ quote t)
and serveLine ()  = serve' (readLine ())
and serve = function (Twelf.OK) -> (issue (Twelf.OK); serveLine ()) | (Twelf.ABORT) -> (issue (Twelf.ABORT); serveLine ())
let rec serveTop (status)  = try serve (status) with Error (msg) -> (print ("Server error: " ^ msg ^ "\n"); serveTop (Twelf.ABORT)) | exn -> (print ("Uncaught exception: " ^ exnMessage exn ^ "\n"); serveTop (Twelf.ABORT))
let rec server (name, _)  = (* ignore server name and arguments *)
 (print (Twelf.version ^ "\n"); Timing.init (); (* initialize timers *)
SigINT.interruptLoop (fun () -> serveTop (Twelf.OK)); OS.Process.success)
 end


(* functor Server *)


module Server = Server (struct module SigINT = SigINT end) (struct module Timing = Timing end) (struct module Lexer = Lexer end) (struct module Twelf = Twelf end)

