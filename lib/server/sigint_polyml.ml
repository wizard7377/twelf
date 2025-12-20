module SigINT : SIGINT = struct let rec interruptLoop (loop : unit -> unit)  = ( (*
	val _ = print
"Upon interrupt at prompt => type\n\
\f to return to top-level of Twelf server\n\
\c to continue Twelf execution\n\
\q to quit the Twelf server\n"
        *)
let origIntHandler = Signal.signal (Posix.Signal.int, Signal.SIG_HANDLE (fun n -> (print "\ninterrupt\n"; Process.interruptConsoleProcesses ()))) in  loop () )
 end


(* structure SigINT *)

