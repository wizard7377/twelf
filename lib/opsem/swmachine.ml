open Basis

module SwMachine
    (Trace : Trace.TRACE)
    (AbsMachine : Absmachine.ABSMACHINE)
    (TMachine : Absmachine.ABSMACHINE) : Absmachine.ABSMACHINE = struct
  (*! structure IntSyn = AbsMachine.IntSyn !*)

  (*! structure CompSyn = AbsMachine.CompSyn !*)

  let rec solve args =
    if Trace.tracing () then TMachine.solve args else AbsMachine.solve args
end

(* functor SwMachine *)
