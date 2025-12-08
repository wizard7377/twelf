(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

module type PARSE_FIXITY =
sig

  (*! module Parsing : PARSING !*)
  module Names : NAMES

  val parseFixity' : ((Names.Qid * Paths.region) * Names.Fixity.fixity) Parsing.parser
  val parseNamePref' : ((Names.Qid * Paths.region)
			* (string list * string list)) Parsing.parser

end;; (* module type PARSE_FIXITY *)
