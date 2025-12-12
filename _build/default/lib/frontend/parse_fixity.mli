(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PARSE_FIXITY =
sig

  (*! structure Parsing : PARSING !*)
  structure Names : NAMES

  val parseFixity' : ((Names.qid * Paths.region) * Names.Fixity.fixity) Parsing.parser
  val parseNamePref' : ((Names.qid * Paths.region)
			* (string list * string list)) Parsing.parser

end (* GEN END SIGNATURE DECLARATION *);  (* signature PARSE_FIXITY *)
