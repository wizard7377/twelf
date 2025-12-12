(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*)

structure UnknownExn =
  UnknownExn ((* GEN BEGIN TAG INSIDE LET *) val exnHistory = fn exn => nil (* GEN END TAG INSIDE LET *));
