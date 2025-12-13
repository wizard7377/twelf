(* Timers collecting statistics about Twelf *)
(* Author: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) Timers (structure Timing' : TIMING)
   : TIMERS =
struct

  structure Timing = Timing'

  (* GEN BEGIN TAG OUTSIDE LET *) val parsing     = Timing.newCenter ("Parsing       ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val recon       = Timing.newCenter ("Reconstruction") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val abstract    = Timing.newCenter ("Abstraction   ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val checking    = Timing.newCenter ("Checking      ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val modes       = Timing.newCenter ("Modes         ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val subordinate = Timing.newCenter ("Subordination ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val terminate   = Timing.newCenter ("Termination   ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val printing    = Timing.newCenter ("Printing      ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val compiling   = Timing.newCenter ("Compiling     ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val solving     = Timing.newCenter ("Solving       ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val coverage    = Timing.newCenter ("Coverage      ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val worlds      = Timing.newCenter ("Worlds        ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val ptrecon     = Timing.newCenter ("ProofRecon    ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val filling     = Timing.newCenter ("Filling       ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val filltabled  = Timing.newCenter ("Filling Tabled") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val splitting   = Timing.newCenter ("Splitting     ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val recursion   = Timing.newCenter ("Recursion     ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val inference   = Timing.newCenter ("Inference     ") (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val delphin     = Timing.newCenter ("Delphin       ") (* GEN END TAG OUTSIDE LET *)

  (* GEN BEGIN TAG OUTSIDE LET *) val centers = [parsing, recon, abstract, checking, modes, subordinate,
                 terminate, printing, compiling, solving, coverage, worlds,
                 ptrecon, filling, filltabled,
                 splitting, recursion, inference, delphin] (* GEN END TAG OUTSIDE LET *)

  (* GEN BEGIN TAG OUTSIDE LET *) val total    = Timing.sumCenter ("Total         ", centers) (* GEN END TAG OUTSIDE LET *)

  (* GEN BEGIN TAG OUTSIDE LET *) val time = Timing.time (* GEN END TAG OUTSIDE LET *)

  fun reset () = List.app Timing.reset centers

  fun check () =
      (List.app (print o Timing.toString) centers;
       print (Timing.sumToString total);
       print "Remember that the success continuation counts into Solving!\n")

  fun show () = (check (); reset ())

end (* GEN END FUNCTOR DECL *);  (* functor Timers *)
