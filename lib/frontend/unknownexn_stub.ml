(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*)

module UnknownExn =
  UnknownExn (let exnHistory = fun exn -> nil);
