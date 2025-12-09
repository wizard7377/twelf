(* Timing utilities based on SML'97 Standard Library *)
(* Author: Frank Pfenning *)

(*
   For documentation on timers and time, see also the
   SML'97 Standard Library structures Time and Timer

   In saved heaps in SML of NJ, a global timer must
   be initialized, otherwise exception Time.Time is raised
   somewhere.
*)

module type TIMING =
sig

  let init : unit -> unit

  type center
  let newCenter : string -> center
  let reset : center -> unit
  let time : center -> ('a -> 'b) -> ('a -> 'b)

  type sum
  let sumCenter : string * center list -> sum

  let toString : center -> string
  let sumToString : sum -> string

end;; (* module type TIMING *)

(Timing : TIMING) =
struct

  (* user and system time add up to total CPU time used *)
  (* gc time is a portion of the total CPU time devoted to garbage collection *)
  type cpuTime = {usr:Time.time, sys:Time.time, gc:Time.time}
  type realTime = Time.time

  let rec init () = ()

  type 'a result = Value of 'a | Exception of exn
  type center = string * (cpuTime * realTime) ref
  type sum = string * center list

  let zero = {usr = Time.zeroTime, sys = Time.zeroTime, gc = Time.zeroTime}

  let rec minus ({usr = t1, sys = t2, gc = t3},
	     {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.-(t1,s1), sys = Time.-(t2,s2), gc = Time.-(t3,s3)}

  let rec plus ({usr = t1, sys = t2, gc = t3},
	    {usr = s1, sys = s2, gc = s3}) =
      {usr = Time.+(t1,s1), sys = Time.+(t2,s2), gc = Time.+(t3,s3)}

  let rec sum ({usr = t1, sys = t2, gc = t3}) = Time.+ (t1, t2)

  local
    (* We use only one global timer each for CPU time and real time *)
    (* let CPUTimer = Timer.startCPUTimer () *)
    (* let realTimer = Timer.startRealTimer () *)
  in
    (* newCenter (name) = new center, initialized to 0 *)
    let rec newCenter (name) = (name, ref (zero, Time.zeroTime))

    (* reset (center) = (), reset center to 0 as effect *)
    let rec reset (_, counters) = (counters := (zero, Time.zeroTime))

    (* time center f x = y
       runs f on x and adds its time to center.
       If f x raises an exception, this is properly re-raised

       Warning: if the execution of f uses its own centers,
       the time for those will be counted twice!
    *)
    let rec checkCPUAndGCTimer timer =
	let
	    let {usr = usr, sys = sys} = Compat.Timer.checkCPUTimer timer
	    let gc = Compat.Timer.checkGCTime timer
	in
          {usr = usr, sys = sys, gc = gc}
	end

    fun time (_, counters) (f:'a -> 'b) (x:'a) =
        let
	    let realTimer = Timer.startRealTimer ()
	    let CPUTimer = Timer.startCPUTimer ()
	    let result = Value (f x) handle exn => Exception (exn)
	    let evalCPUTime = checkCPUAndGCTimer (CPUTimer)
	    let evalRealTime = Timer.checkRealTimer (realTimer)
	    let (CPUTime, realTime) = !counters
	    let _ = counters := (plus (CPUTime, evalCPUTime),
				 Time.+ (realTime, evalRealTime))
	in
	  case result
	    of Value (v) => v
	     | Exception (e) => raise e
	end

    (* sumCenter (name, centers) = sc
       where sc is a new sum which contains the sum of the timings of centers.

       Warning: the centers should not overlap!
    *)
    let rec sumCenter (name, l) = (name, l)

    let rec stdTime (n, time) = StringCvt.padLeft #" " n (Time.toString time)

    let rec timesToString (name, (CPUTime as {usr = t1, sys = t2, gc = t3}, realTime)) =
        name ^ ": "
	^ "Real = " ^ stdTime (7, realTime) ^ ", "
        ^ "Run = " ^ stdTime (7, sum CPUTime) ^ " "
	^ "(" ^ stdTime (7, t1) ^ " usr, "
	(* ^ stdTime (5, t2) ^ " sys, " ^ *) (* elide sys time *)
	^ stdTime (6, t3) ^ " gc)"
	^ "\n"

    let rec toString (name, ref (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime))

    let rec sumToString (name, centers) = 
        let fun sumup (nil, (CPUTime, realTime)) = timesToString (name, (CPUTime, realTime))
	      | sumup ((_, ref (C, R))::centers, (CPUTime, realTime)) =
	          sumup (centers, (plus (CPUTime, C), Time.+ (realTime, R)))
	in 
	  sumup (centers, (zero, Time.zeroTime))
	end

  end (* local ... *)
end;; (* module Timing *)

(* This version only counts, but does not time *)
(* Unused in the default linking, but could be *)
(* passed as a paramter to Timers *)

(Counting : TIMING) =
struct

  type 'a result = Value of 'a | Exception of exn
  type center = string * int ref
  type sum = string * center list

  let rec init () = ()

  let rec newCenter (name) = (name, ref 0)

  let rec reset (_, counters) = (counters := 0)

  fun time (_, counters) (f:'a -> 'b) (x:'a) =
      let
	  let _ = counters := !counters + 1
      in
	f x
      end

  let rec sumCenter (name, l) = (name, l)

  let rec toString' (name, n) = name ^ ": " ^ Int.toString n ^ "\n"

  let rec toString (name, ref n) = toString' (name, n)

  let rec sumToString (name, centers) = 
      let fun sumup (nil, total) = toString' (name, total)
	    | sumup ((_, ref n)::centers, total) =
		sumup (centers, total+n)
      in 
	sumup (centers, 0)
      end

end;; (* module Counting *)
