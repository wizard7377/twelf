(* Compatibility shim from Basis-current TextIO to Basis-97 TextIO *)
(* Author: Christopher Richards *)

structure CompatTextIO97 :> COMPAT_TEXT_IO =
struct
  (* GEN BEGIN TAG INSIDE LET *) fun inputLine instream =
      let
  	val line = TextIO.inputLine instream
      in
  	case line of
  	    ""  => NONE
  	  | str => SOME str
      end (* GEN END TAG INSIDE LET *)
end;
