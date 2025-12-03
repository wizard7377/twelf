(* Parsing Queries *) 
(* Author: Frank Pfenning *)

module type PARSE_QUERY =
sig

  (*! module Parsing : PARSING !*)
  module ExtQuery : EXTQUERY

  val parseQuery' : ExtQuery.query Parsing.parser
  val parseSolve' : (ExtQuery.define list * ExtQuery.solve) Parsing.parser

end;  (* module type PARSE_QUERY *)
