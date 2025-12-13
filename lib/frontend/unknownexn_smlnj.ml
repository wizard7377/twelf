(* Print exception trace in unknownExn.  Both SML/NJ and MLton have
   SMLofNJ.exnHistory.
*)

structure UnknownExn =
  UnknownExn ((* GEN BEGIN TAG OUTSIDE LET *) val exnHistory = SMLofNJ.exnHistory (* GEN END TAG OUTSIDE LET *));
