module SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
      (SMLofNJ.Cont.callcc
       (fun k -> (Signals.setHandler (Signals.sigINT,
				     Signals.HANDLER (fun _ -> (print "\ninterrupt\n"; k)));
		 ()));
       loop ())

end;  (* module SigINT *)
