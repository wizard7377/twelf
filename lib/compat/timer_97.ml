(* Compatibility shim from Basis-current Timer to Basis-97 Timer *)
(* Author: Christopher Richards *)

structure CompatTimer97 :> COMPAT_TIMER =
struct
  fun checkCPUTimer timer =
      let
  	(* GEN BEGIN TAG OUTSIDE LET *) val {usr = usr, sys = sys, gc = gc} = Timer.checkCPUTimer timer (* GEN END TAG OUTSIDE LET *)
      in
  	{usr = usr, sys = sys}
      end
      
  fun checkGCTime timer =
      let
  	(* GEN BEGIN TAG OUTSIDE LET *) val {gc = gc, ...} = Timer.checkCPUTimer timer (* GEN END TAG OUTSIDE LET *)
      in
  	gc
      end
end;
