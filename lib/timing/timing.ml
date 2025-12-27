open Basis

(* Timing utilities based on SML'97 Standard Library *)

(* Author: Frank Pfenning *)

(*
   For documentation on timers and time, see also the
   SML'97 Standard Library structures Time and Timer

   In saved heaps in SML of NJ, a global timer must
   be initialized, otherwise exception Time.t is raised
   somewhere.
*)

module type TIMING = sig
  val init : unit -> unit

  type center

  val newCenter : string -> center
  val reset : center -> unit
  val time : center -> ('a -> 'b) -> 'a -> 'b

  type sum

  val sumCenter : string * center list -> sum
  val toString : center -> string
  val sumToString : sum -> string
end

(* signature TIMING *)
open Basis

module Timing : TIMING = struct
  (* user and system time add up to total CPU time used *)

  (* gc time is a portion of the total CPU time devoted to garbage collection *)

  type cpuTime = { usr : Time.t; sys : Time.t; gc : Time.t }
  type realTime = Time.t

  let rec init () = ()

  type 'a result = Value of 'a | Exception of exn
  type center = string * (cpuTime * realTime) ref
  type sum = string * center list

  let zero = { usr = Time.zeroTime; sys = Time.zeroTime; gc = Time.zeroTime }

  let rec minus
      ({ usr = t1; sys = t2; gc = t3 }, { usr = s1; sys = s2; gc = s3 }) =
    {
      usr = Time.( - ) (t1, s1);
      sys = Time.( - ) (t2, s2);
      gc = Time.( - ) (t3, s3);
    }

  let rec plus ({ usr = t1; sys = t2; gc = t3 }, { usr = s1; sys = s2; gc = s3 })
      =
    {
      usr = Time.( + ) (t1, s1);
      sys = Time.( + ) (t2, s2);
      gc = Time.( + ) (t3, s3);
    }

  let rec sum { usr = t1; sys = t2; gc = t3 } = Time.( + ) (t1, t2)
  (* We use only one global timer each for_sml CPU time and real time *)

  (* val CPUTimer = Timer.startCPUTimer () *)

  (* val realTimer = Timer.startRealTimer () *)

  (* newCenter (name) = new center, initialized to 0 *)

  let rec newCenter name = (name, ref (zero, Time.zeroTime))
  (* reset (center) = (), reset center to effect *)

  let rec reset (_, counters) = counters := (zero, Time.zeroTime)
  (* time center f x = y
       runs f on x and adds its time to center.
       If f x raises an exception, this is properly re-raised

       Warning: if the execution of f uses its own centers,
       the time for_sml those will be counted twice!
    *)

  let rec checkCPUAndGCTimer timer =
    let { Timer.usr; sys } = Timer.checkCPUTimer timer in
    (* GC time not available in OCaml's basic Timer - use 0 *)
    let gc = Time.zeroTime in
    { usr = Time.fromReal usr; sys = Time.fromReal sys; gc }

  let rec time (_, counters) (f : 'a -> 'b) (x : 'a) =
    let realTimer = Timer.startRealTimer () in
    let cpuTimer = Timer.startCPUTimer () in
    let result = try Value (f x) with exn -> Exception exn in
    let evalCPUTime = checkCPUAndGCTimer cpuTimer in
    let evalRealTime = Time.fromReal (Timer.checkRealTimer realTimer) in
    let cpuTime, realTime = !counters in
    let _ =
      counters :=
        (plus (cpuTime, evalCPUTime), Time.( + ) (realTime, evalRealTime))
    in
    match result with Value v -> v | Exception e -> raise e
  (* sumCenter (name, centers) = sc
       where sc is a new sum which contains the sum of the timings of centers.

       Warning: the centers should not overlap!
    *)

  let rec sumCenter (name, l) = (name, l)
  let rec stdTime (n, time) = StringCvt.padLeft ' ' n (Time.toString time)

  let rec timesToString (name, (cpuTime, realTime)) =
    name ^ ": " ^ "Real = "
    ^ stdTime (7, realTime)
    ^ ", " ^ "Run = "
    ^ stdTime (7, sum cpuTime)
    ^ " " ^ "("
    ^ stdTime (7, cpuTime.usr)
    ^ " usr, " (* ^ stdTime (5, cpuTime.sys) ^ " sys, " ^ *)
    (* elide sys time *)
    ^ stdTime (6, cpuTime.gc)
    ^ " gc)" ^ "\n"

  let rec toString (name, { contents = cpuTime, realTime }) =
    timesToString (name, (cpuTime, realTime))

  let rec sumToString (name, centers) =
    let rec sumup = function
      | [], (cpuTime, realTime) -> timesToString (name, (cpuTime, realTime))
      | (_, { contents = c, r }) :: centers, (cpuTime, realTime) ->
          sumup (centers, (plus (cpuTime, c), Time.( + ) (realTime, r)))
    in
    sumup (centers, (zero, Time.zeroTime))
  (* local ... *)
end

(* structure Timing *)

(* This version only counts, but does not time *)

(* Unused in the default linking, but could be *)

(* a paramter to Timers *)

module Counting : TIMING = struct
  type 'a result = Value of 'a | Exception of exn
  type center = string * int ref
  type sum = string * center list

  let rec init () = ()
  let rec newCenter name = (name, ref 0)
  let rec reset (_, counters) = counters := 0

  let rec time (_, counters) (f : 'a -> 'b) (x : 'a) =
    let _ = counters := !counters + 1 in
    f x

  let rec sumCenter (name, l) = (name, l)
  let rec toString' (name, n) = name ^ ": " ^ Integer.toString n ^ "\n"
  let rec toString (name, { contents = n }) = toString' (name, n)

  let rec sumToString (name, centers) =
    let rec sumup = function
      | [], total -> toString' (name, total)
      | (_, { contents = n }) :: centers, total -> sumup (centers, total + n)
    in
    sumup (centers, 0)
end

(* structure Counting *)
