(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PARSE_MODE =
sig

  (*! structure Parsing : PARSING !*)
  structure ExtModes: EXTMODES

  val parseMode' : (ExtModes.modedec list) Parsing.parser

end (* GEN END SIGNATURE DECLARATION *);  (* signature PARSE_MODE *)
