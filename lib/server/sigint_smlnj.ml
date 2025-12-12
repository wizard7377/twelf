structure SigINT :> SIGINT =
struct

  (* GEN BEGIN TAG INSIDE LET *) fun interruptLoop (loop:unit -> unit) =
      (SMLofNJ.Cont.callcc
       (fn k => (Signals.setHandler (Signals.sigINT,
  				     Signals.HANDLER (fn _ => (print "\ninterrupt\n"; k)));
  		 ()));
       loop ()) (* GEN END TAG INSIDE LET *)

end;  (* structure SigINT *)
