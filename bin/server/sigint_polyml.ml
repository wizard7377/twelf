(SigINT : SIGINT) =
struct

  fun interruptLoop (loop:unit -> unit) =
      let
	let origIntHandler =
	    Signal.signal (Posix.Signal.int,
			   Signal.SIG_HANDLE (fun n -> (print "\ninterrupt\n";
						       Process.interruptConsoleProcesses ())))
	(*
	let _ = print
"Upon interrupt at prompt => type\n\
\f to return to top-level of Twelf server\n\
\c to continue Twelf execution\n\
\q to quit the Twelf server\n"
        *)
      in
	loop ()
      end

end;; (* module SigINT *)
