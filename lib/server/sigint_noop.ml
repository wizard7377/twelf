open Basis

module SigINT : Sigint.SIGINT = struct
  let rec interruptLoop (loop : unit -> unit) = loop ()
end
