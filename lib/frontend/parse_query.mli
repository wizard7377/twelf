(* Parsing Queries *) 
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PARSE_QUERY =
sig

  (*! structure Parsing : PARSING !*)
  structure ExtQuery : EXTQUERY

  val parseQuery' : ExtQuery.query Parsing.parser
  val parseSolve' : (ExtQuery.define list * ExtQuery.solve) Parsing.parser

end (* GEN END SIGNATURE DECLARATION *);  (* signature PARSE_QUERY *)
