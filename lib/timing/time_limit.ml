(* time-limit.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 * Modified: Brigitte Pientka
 *)

structure TimeLimit : sig
    exception TimeOut
    val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  end = struct

    exception TimeOut

    fun (* GEN BEGIN FUN FIRST *) timeLimit NONE f x = f x (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) timeLimit (SOME t) f x = 
      let
      	(* GEN BEGIN TAG OUTSIDE LET *) val _ = print ("TIME LIMIT : " ^ Time.toString t ^ "sec \n") (* GEN END TAG OUTSIDE LET *)
      	(* GEN BEGIN TAG OUTSIDE LET *) val setitimer = SMLofNJ.IntervalTimer.setIntTimer (* GEN END TAG OUTSIDE LET *)
      
      	fun timerOn () = ignore(setitimer (SOME t))
      
      	fun timerOff () = ignore(setitimer NONE)
      
      	(* GEN BEGIN TAG OUTSIDE LET *) val escapeCont = SMLofNJ.Cont.callcc ((* GEN BEGIN FUNCTION EXPRESSION *) fn k => (
      		SMLofNJ.Cont.callcc ((* GEN BEGIN FUNCTION EXPRESSION *) fn k' => (SMLofNJ.Cont.throw k k') (* GEN END FUNCTION EXPRESSION *));
      		timerOff();
      		raise TimeOut) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
      
      	fun handler _ = escapeCont
      
      in
      	Signals.setHandler (Signals.sigALRM, Signals.HANDLER handler);
      	timerOn(); 
      	((f x) handle ex => (timerOff(); raise ex))
      	  before timerOff()
      end (* GEN END FUN BRANCH *)

  end; (* TimeLimit *)
