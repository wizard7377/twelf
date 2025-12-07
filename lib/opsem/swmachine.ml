let recctor SwMachine (module Trace : TRACE
                   module AbsMachine : ABSMACHINE
                   module TMachine : ABSMACHINE): ABSMACHINE =
                   (*! sharing TMachine.IntSyn = AbsMachine.IntSyn !*)
                   (*! sharing TMachine.CompSyn = AbsMachine.CompSyn !*)
struct

  (*! module IntSyn = AbsMachine.IntSyn !*)
  (*! module CompSyn = AbsMachine.CompSyn !*)

  fun solve args =
    if Trace.tracing ()
      then TMachine.solve args
    else  AbsMachine.solve args

end;  (* functor SwMachine *)

