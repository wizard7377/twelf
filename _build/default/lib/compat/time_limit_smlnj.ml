(* SML/NJ implementation of timeLimit *)
(* Other implementations possible via ALRM signal? *)

structure TimeLimit :> TIME_LIMIT =
struct

    exception TimeOut

    fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) timeLimit NONE f x = f x (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
      | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) timeLimit (SOME t) f x = 
      let
      	val _ = print ("TIME LIMIT : " ^ Time.toString t ^ "sec \n")
      	val setitimer = SMLofNJ.IntervalTimer.setIntTimer
      
      	fun timerOn () = ignore(setitimer (SOME t))
      
      	fun timerOff () = ignore(setitimer NONE)
      
      	val escapeCont = SMLofNJ.Cont.callcc (fn k => (
      		SMLofNJ.Cont.callcc (fn k' => (SMLofNJ.Cont.throw k k'));
      		timerOff();
      		raise TimeOut))
      
      	fun handler _ = escapeCont
      
      in
      	Signals.setHandler (Signals.sigALRM, Signals.HANDLER handler);
      	timerOn(); 
      	((f x) handle ex => (timerOff(); raise ex))
      	  before timerOff()
      end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  end; (* TimeLimit *)
