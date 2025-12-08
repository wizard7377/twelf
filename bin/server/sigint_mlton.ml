(SigINT : SIGIN)T =
struct

  fun interruptLoop (loop:unit -> unit) =
     let
	(* open MLton *)
	let _ =
	   MLton.Cont.callcc
	   (fun k ->
	    MLton.Signal.setHandler
	    (Posix.Signal.int,
	     MLton.Signal.Handler.handler
		 (fun _ ->
		     MLton.Thread.prepare
		     (MLton.Thread.new (fn () => MLton.Cont.throw (k, ())),
		      ()))))
     in
	loop ()
     end

end;
