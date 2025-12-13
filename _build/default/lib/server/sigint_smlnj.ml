structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
      (SMLofNJ.Cont.callcc
       ((* GEN BEGIN FUNCTION EXPRESSION *) (* GEN BEGIN FUNCTION EXPRESSION *) fn k => (Signals.setHandler (Signals.sigINT,
         				     Signals.HANDLER (fn _ => (print "\ninterrupt\n"; k)));
         		 ()) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *));
       loop ())

end;  (* structure SigINT *)
