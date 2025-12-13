(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*)

structure UnknownExn =
  UnknownExn ((* GEN BEGIN TAG OUTSIDE LET *) val exnHistory = (* GEN BEGIN FUNCTION EXPRESSION *) fn exn => nil (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *));
