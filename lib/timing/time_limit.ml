(* time-limit.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 * Modified: Brigitte Pientka
 *)

(TimeLimit : sig)
    exception TimeOut
    let timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  end = struct

    exception TimeOut

    let rec timeLimit = function NONE f x -> f x
      | (SOME t) f x -> 
      let
	let _ = print ("TIME LIMIT : " ^ Time.toString t ^ "sec \n")
	let setitimer = SMLofNJ.IntervalTimer.setIntTimer

	fun timerOn () = ignore(setitimer (SOME t))

	fun timerOff () = ignore(setitimer NONE)

	let escapeCont = SMLofNJ.Cont.callcc (fun k -> (
		SMLofNJ.Cont.callcc (fn k' => (SMLofNJ.Cont.throw k k'));
		timerOff();
		raise TimeOut))

	fun handler _ = escapeCont

      in
	Signals.setHandler (Signals.sigALRM, Signals.HANDLER handler);
	timerOn(); 
	((f x) handle ex => (timerOff(); raise ex))
	  before timerOff()
      end

  end; (* TimeLimit *)
