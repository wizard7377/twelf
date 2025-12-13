structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
     let
  	(* open MLton *)
  	(* GEN BEGIN TAG OUTSIDE LET *) val _ =
  	   MLton.Cont.callcc
  	   ((* GEN BEGIN FUNCTION EXPRESSION *) fn k =>
  	    MLton.Signal.setHandler
  	    (Posix.Signal.int,
  	     MLton.Signal.Handler.handler
  		 ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ =>
  		     MLton.Thread.prepare
  		     (MLton.Thread.new ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => MLton.Cont.throw (k, ()) (* GEN END FUNCTION EXPRESSION *)),
  		      ()) (* GEN END FUNCTION EXPRESSION *))) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
     in
  	loop ()
     end

end;
