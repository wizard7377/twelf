(** Timer module - SML Basis Library TIMER signature *)

module type TIMER = sig
  type cpu_timer
  type real_timer
  type cpu_time = {usr : Time.Time.time; sys : Time.Time.time}

  val startCPUTimer : unit -> cpu_timer
  val checkCPUTimer : cpu_timer -> cpu_time

  val startRealTimer : unit -> real_timer
  val checkRealTimer : real_timer -> Time.Time.time

  val totalCPUTimer : unit -> cpu_timer
  val totalRealTimer : unit -> real_timer
end

module Timer : TIMER = struct
  type cpu_timer = float  (* Start time *)
  type real_timer = float (* Start time *)
  type cpu_time = {usr : Time.Time.time; sys : Time.Time.time}

  let startCPUTimer () = Sys.time ()

  let checkCPUTimer start =
    let elapsed = Sys.time () -. start in
    { usr = elapsed; sys = 0.0 }

  let startRealTimer () = Unix.gettimeofday ()

  let checkRealTimer start =
    Unix.gettimeofday () -. start

  let totalCPUTimer () = 0.0
  let totalRealTimer () = Unix.gettimeofday ()
end
