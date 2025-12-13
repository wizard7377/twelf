structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
      let
  	(* GEN BEGIN TAG OUTSIDE LET *) val origIntHandler =
  	    Signal.signal (Posix.Signal.int,
  			   Signal.SIG_HANDLE ((* GEN BEGIN FUNCTION EXPRESSION *) fn n => (print "\ninterrupt\n";
  						       Process.interruptConsoleProcesses ()) (* GEN END FUNCTION EXPRESSION *))) (* GEN END TAG OUTSIDE LET *)
  	(*
  	val _ = print
  "Upon interrupt at prompt => type\n\
  \f to return to top-level of Twelf server\n\
  \c to continue Twelf execution\n\
  \q to quit the Twelf server\n"
        *)
      in
  	loop ()
      end

end;  (* structure SigINT *)
