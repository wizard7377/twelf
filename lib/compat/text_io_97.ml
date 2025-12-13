(* Compatibility shim from Basis-current TextIO to Basis-97 TextIO *)
(* Author: Christopher Richards *)

structure CompatTextIO97 :> COMPAT_TEXT_IO =
struct
  fun inputLine instream =
      let
  	(* GEN BEGIN TAG OUTSIDE LET *) val line = TextIO.inputLine instream (* GEN END TAG OUTSIDE LET *)
      in
  	case line of
  	    ""  => NONE
  	  | str => SOME str
      end
end;
