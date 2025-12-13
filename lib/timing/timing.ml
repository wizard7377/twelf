(* Timing utilities based on SML'97 Standard Library *)
(* Author: Frank Pfenning *)

(*
   For documentation on timers and time, see also the
   SML'97 Standard Library structures Time and Timer

   In saved heaps in SML of NJ, a global timer must
   be initialized, otherwise exception Time.Time is raised
   somewhere.
*)

(* GEN BEGIN SIGNATURE DECLARATION *) signature TIMING =
sig

  val init : unit -> unit

  type center
  val newCenter : string -> center
  val reset : center -> unit
  val time : center -> ('a -> 'b) -> ('a -> 'b)

  type sum
  val sumCenter : string * center list -> sum

  val toString : center -> string
  val sumToString : sum -> string

end (* GEN END SIGNATURE DECLARATION *);  (* signature TIMING *)

structure Timing :> TIMING =
struct

  (* user and system time add up to total CPU time used *)
  (* gc time is a portion of the total CPU time devoted to garbage collection *)
  type cpu_time = {usr:Time.time, sys:Time.time, gc:Time.time}
  type real_time = Time.time

  fun init () = ()

  datatype 'a result = Value of 'a | Exception of exn
  type center = string * (cpu_time * real_time) ref
  type sum = string * center list

  (* GEN BEGIN TAG OUTSIDE LET *) val zero = {usr = Time.zeroTime, sys = Time.zeroTime, gc = Time.zeroTime} (* GEN END TAG OUTSIDE LET *)

  fun minus ({usr = t1, sys = t2, gc = t3},
  	     {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.-(t1,s1), sys = Time.-(t2,s2), gc = Time.-(t3,s3)}

  fun plus ({usr = t1, sys = t2, gc = t3},
  	    {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.+(t1,s1), sys = Time.+(t2,s2), gc = Time.+(t3,s3)}

  fun sum ({usr = t1, sys = t2, gc = t3}) = Time.+ (t1, t2)

  local
    (* We use only one global timer each for CPU time and real time *)
    (* val CPUTimer = Timer.startCPUTimer () *)
    (* val realTimer = Timer.startRealTimer () *)
  in
    (* newCenter (name) = new center, initialized to 0 *)
    fun newCenter (name) = (name, ref (zero, Time.zeroTime))

    (* reset (center) = (), reset center to 0 as effect *)
    fun reset (_, counters) = (counters := (zero, Time.zeroTime))

    (* time center f x = y
       runs f on x and adds its time to center.
       If f x raises an exception, this is properly re-raised

       Warning: if the execution of f uses its own centers,
       the time for those will be counted twice!
    *)
    fun checkCPUAndGCTimer timer =
    	let
    	    (* GEN BEGIN TAG OUTSIDE LET *) val {usr = usr, sys = sys} = Compat.Timer.checkCPUTimer timer (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val gc = Compat.Timer.checkGCTime timer (* GEN END TAG OUTSIDE LET *)
    	in
          {usr = usr, sys = sys, gc = gc}
    	end

    fun time (_, counters) (f:'a -> 'b) (x:'a) =
        let
    	    (* GEN BEGIN TAG OUTSIDE LET *) val realTimer = Timer.startRealTimer () (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val CPUTimer = Timer.startCPUTimer () (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val result = Value (f x) handle exn => Exception (exn) (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val evalCPUTime = checkCPUAndGCTimer (CPUTimer) (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val evalRealTime = Timer.checkRealTimer (realTimer) (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val (CPUTime, realTime) = !counters (* GEN END TAG OUTSIDE LET *)
    	    (* GEN BEGIN TAG OUTSIDE LET *) val _ = counters := (plus (CPUTime, evalCPUTime),
    				 Time.+ (realTime, evalRealTime)) (* GEN END TAG OUTSIDE LET *)
    	in
    	  case result
    	    of Value (v) => v
    	     | Exception (e) => raise e
    	end

    (* sumCenter (name, centers) = sc
       where sc is a new sum which contains the sum of the timings of centers.

       Warning: the centers should not overlap!
    *)
    fun sumCenter (name, l) = (name, l)

    fun stdTime (n, time) = StringCvt.padLeft #" " n (Time.toString time)

    fun timesToString (name, (CPUTime as {usr = t1, sys = t2, gc = t3}, realTime)) =
        name ^ ": "
    	^ "Real = " ^ stdTime (7, realTime) ^ ", "
        ^ "Run = " ^ stdTime (7, sum CPUTime) ^ " "
    	^ "(" ^ stdTime (7, t1) ^ " usr, "
    	(* ^ stdTime (5, t2) ^ " sys, " ^ *) (* elide sys time *)
    	^ stdTime (6, t3) ^ " gc)"
    	^ "\n"

    fun toString (name, ref (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime))

    fun sumToString (name, centers) = 
        let fun (* GEN BEGIN FUN FIRST *) sumup (nil, (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime)) (* GEN END FUN FIRST *)
    	      | (* GEN BEGIN FUN BRANCH *) sumup ((_, ref (C, R))::centers, (CPUTime, realTime)) =
    	          sumup (centers, (plus (CPUTime, C), Time.+ (realTime, R))) (* GEN END FUN BRANCH *)
    	in 
    	  sumup (centers, (zero, Time.zeroTime))
    	end

  end (* local ... *)
end;  (* structure Timing *)

(* This version only counts, but does not time *)
(* Unused in the default linking, but could be *)
(* passed as a paramter to Timers *)

structure Counting :> TIMING =
struct

  datatype 'a result = Value of 'a | Exception of exn
  type center = string * int ref
  type sum = string * center list

  fun init () = ()

  fun newCenter (name) = (name, ref 0)

  fun reset (_, counters) = (counters := 0)

  fun time (_, counters) (f:'a -> 'b) (x:'a) =
      let
  	  (* GEN BEGIN TAG OUTSIDE LET *) val _ = counters := !counters + 1 (* GEN END TAG OUTSIDE LET *)
      in
  	f x
      end

  fun sumCenter (name, l) = (name, l)

  fun toString' (name, n) = name ^ ": " ^ Int.toString n ^ "\n"

  fun toString (name, ref n) = toString' (name, n)

  fun sumToString (name, centers) = 
      let fun (* GEN BEGIN FUN FIRST *) sumup (nil, total) = toString' (name, total) (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) sumup ((_, ref n)::centers, total) =
  		sumup (centers, total+n) (* GEN END FUN BRANCH *)
      in 
  	sumup (centers, 0)
      end

end;  (* structure Counting *)
