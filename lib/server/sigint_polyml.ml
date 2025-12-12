structure SigINT :> SIGINT =
struct

  (* GEN BEGIN TAG INSIDE LET *) fun interruptLoop (loop:unit -> unit) =
      let
  	val origIntHandler =
  	    Signal.signal (Posix.Signal.int,
  			   Signal.SIG_HANDLE (fn n => (print "\ninterrupt\n";
  						       Process.interruptConsoleProcesses ())))
  	(*
  	val _ = print
  "Upon interrupt at prompt => type\n\
  \f to return to top-level of Twelf server\n\
  \c to continue Twelf execution\n\
  \q to quit the Twelf server\n"
        *)
      in
  	loop ()
      end (* GEN END TAG INSIDE LET *)

end;  (* structure SigINT *)
