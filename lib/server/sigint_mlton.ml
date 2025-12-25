open Basis

module SigINT : Sigint.SIGINT = struct
  let rec interruptLoop (loop : unit -> unit) =
    (* open MLton *)
    let _ =
      MLton.Cont.callcc (fun k ->
          MLton.Signal.setHandler
            ( Posix.Signal.int,
              MLton.Signal.Handler.handler (fun _ ->
                  MLton.Thread.prepare
                    (MLton.Thread.new_ (fun () -> MLton.Cont.throw (k, ())), ()))
            ))
    in
    loop ()
end
