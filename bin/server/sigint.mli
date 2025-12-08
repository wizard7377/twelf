module type SIGINT =
sig

  val interruptLoop : (unit -> unit) -> unit

end;; (* module type SIGINT *)
