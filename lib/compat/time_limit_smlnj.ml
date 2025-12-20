(* SML/NJ implementation of timeLimit *)


(* Other implementations possible via ALRM signal? *)


module TimeLimit : TIME_LIMIT = struct exception TimeOut
let rec timeLimit = function (None, f, x) -> f x | ((Some t), f, x) -> ( let _ = print ("TIME LIMIT : " ^ Time.toString t ^ "sec \n") in let setitimer = SMLofNJ.IntervalTimer.setIntTimer in let rec timerOn ()  = ignore (setitimer (Some t)) in let rec timerOff ()  = ignore (setitimer None) in let escapeCont = SMLofNJ.Cont.callcc (fun k -> (SMLofNJ.Cont.callcc (fun k' -> (SMLofNJ.Cont.throw k k')); timerOff (); raise (TimeOut))) in let rec handler _  = escapeCont in  Signals.setHandler (Signals.sigALRM, Signals.HANDLER handler); timerOn (); (try (f x) with ex -> (timerOff (); raise (ex))) before timerOff () )
 end


(* TimeLimit *)

