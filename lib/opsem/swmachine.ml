module SwMachine (Trace : TRACE) (AbsMachine : ABSMACHINE) (TMachine : ABSMACHINE) : ABSMACHINE = struct (*! structure IntSyn = AbsMachine.IntSyn !*)

(*! structure CompSyn = AbsMachine.CompSyn !*)

let rec solve args  = if Trace.tracing () then TMachine.solve args else AbsMachine.solve args
 end


(* functor SwMachine *)

