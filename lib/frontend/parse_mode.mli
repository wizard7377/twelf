(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

module type PARSE_MODE =
sig

  (*! module Parsing : PARSING !*)
  module ExtModes: EXTMODES

  val parseMode' : (ExtModes.modedec list) Parsing.parser

end;  (* module type PARSE_MODE *)
