module SwMachine (Trace : TRACE)
   (AbsMachine : ABSMACHINE)
   (TMachine : ABSMACHINE): ABSMACHINE =
                   (*! sharing TMachine.IntSyn = AbsMachine.IntSyn !*)
                   (*! sharing TMachine.CompSyn = AbsMachine.CompSyn !*)
struct

  (*! module IntSyn = AbsMachine.IntSyn !*)
  (*! module CompSyn = AbsMachine.CompSyn !*)

  let rec solve args =
    if Trace.tracing ()
      then TMachine.solve args
    else  AbsMachine.solve args

end;; (* functor SwMachine *)

