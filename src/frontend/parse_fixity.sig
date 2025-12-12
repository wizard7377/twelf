(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_FIXITY =
sig

  (*! structure Parsing : PARSING !*)
  structure Names : NAMES

  val parseFixity' : ((Names.qid * Paths.region) * Names.Fixity.fixity) Parsing.parser
  val parseNamePref' : ((Names.qid * Paths.region)
			* (string list * string list)) Parsing.parser

end;  (* signature PARSE_FIXITY *)
