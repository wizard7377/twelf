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

  (* GEN BEGIN TAG INSIDE LET *) fun init () = () (* GEN END TAG INSIDE LET *)

  datatype 'a result = Value of 'a | Exception of exn
  type center = string * (cpu_time * real_time) ref
  type sum = string * center list

  (* GEN BEGIN TAG INSIDE LET *) val zero = {usr = Time.zeroTime, sys = Time.zeroTime, gc = Time.zeroTime} (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun minus ({usr = t1, sys = t2, gc = t3},
  	     {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.-(t1,s1), sys = Time.-(t2,s2), gc = Time.-(t3,s3)} (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun plus ({usr = t1, sys = t2, gc = t3},
  	    {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.+(t1,s1), sys = Time.+(t2,s2), gc = Time.+(t3,s3)} (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun sum ({usr = t1, sys = t2, gc = t3}) = Time.+ (t1, t2) (* GEN END TAG INSIDE LET *)

  local
    (* We use only one global timer each for CPU time and real time *)
    (* val CPUTimer = Timer.startCPUTimer () *)
    (* val realTimer = Timer.startRealTimer () *)
  in
    (* newCenter (name) = new center, initialized to 0 *)
    (* GEN BEGIN TAG INSIDE LET *) fun newCenter (name) = (name, ref (zero, Time.zeroTime)) (* GEN END TAG INSIDE LET *)

    (* reset (center) = (), reset center to 0 as effect *)
    (* GEN BEGIN TAG INSIDE LET *) fun reset (_, counters) = (counters := (zero, Time.zeroTime)) (* GEN END TAG INSIDE LET *)

    (* time center f x = y
       runs f on x and adds its time to center.
       If f x raises an exception, this is properly re-raised

       Warning: if the execution of f uses its own centers,
       the time for those will be counted twice!
    *)
    (* GEN BEGIN TAG INSIDE LET *) fun checkCPUAndGCTimer timer =
    	let
    	    val {usr = usr, sys = sys} = Compat.Timer.checkCPUTimer timer
    	    val gc = Compat.Timer.checkGCTime timer
    	in
          {usr = usr, sys = sys, gc = gc}
    	end (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun time (_, counters) (f:'a -> 'b) (x:'a) =
        let
    	    val realTimer = Timer.startRealTimer ()
    	    val CPUTimer = Timer.startCPUTimer ()
    	    val result = Value (f x) handle exn => Exception (exn)
    	    val evalCPUTime = checkCPUAndGCTimer (CPUTimer)
    	    val evalRealTime = Timer.checkRealTimer (realTimer)
    	    val (CPUTime, realTime) = !counters
    	    val _ = counters := (plus (CPUTime, evalCPUTime),
    				 Time.+ (realTime, evalRealTime))
    	in
    	  case result
    	    of Value (v) => v
    	     | Exception (e) => raise e
    	end (* GEN END TAG INSIDE LET *)

    (* sumCenter (name, centers) = sc
       where sc is a new sum which contains the sum of the timings of centers.

       Warning: the centers should not overlap!
    *)
    (* GEN BEGIN TAG INSIDE LET *) fun sumCenter (name, l) = (name, l) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun stdTime (n, time) = StringCvt.padLeft #" " n (Time.toString time) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun timesToString (name, (CPUTime as {usr = t1, sys = t2, gc = t3}, realTime)) =
        name ^ ": "
    	^ "Real = " ^ stdTime (7, realTime) ^ ", "
        ^ "Run = " ^ stdTime (7, sum CPUTime) ^ " "
    	^ "(" ^ stdTime (7, t1) ^ " usr, "
    	(* ^ stdTime (5, t2) ^ " sys, " ^ *) (* elide sys time *)
    	^ stdTime (6, t3) ^ " gc)"
    	^ "\n" (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun toString (name, ref (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime)) (* GEN END TAG INSIDE LET *)

    (* GEN BEGIN TAG INSIDE LET *) fun sumToString (name, centers) = 
        let fun sumup (nil, (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime))
    	      | sumup ((_, ref (C, R))::centers, (CPUTime, realTime)) =
    	          sumup (centers, (plus (CPUTime, C), Time.+ (realTime, R)))
    	in 
    	  sumup (centers, (zero, Time.zeroTime))
    	end (* GEN END TAG INSIDE LET *)

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

  (* GEN BEGIN TAG INSIDE LET *) fun init () = () (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun newCenter (name) = (name, ref 0) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun reset (_, counters) = (counters := 0) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun time (_, counters) (f:'a -> 'b) (x:'a) =
      let
  	  val _ = counters := !counters + 1
      in
  	f x
      end (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun sumCenter (name, l) = (name, l) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun toString' (name, n) = name ^ ": " ^ Int.toString n ^ "\n" (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun toString (name, ref n) = toString' (name, n) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun sumToString (name, centers) = 
      let fun sumup (nil, total) = toString' (name, total)
  	    | sumup ((_, ref n)::centers, total) =
  		sumup (centers, total+n)
      in 
  	sumup (centers, 0)
      end (* GEN END TAG INSIDE LET *)

end;  (* structure Counting *)
