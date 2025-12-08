(* Parsing Signature Entries *) 
(* Author: Frank Pfenning *)

module type PARSE_CONDEC =
sig

  (*! module Parsing : PARSING !*)
  module ExtConDec : EXTCONDEC

  val parseConDec' : ExtConDec.condec Parsing.parser
  val parseAbbrev'  : ExtConDec.condec Parsing.parser
  val parseClause' : ExtConDec.condec Parsing.parser

end;; (* module type PARSE_CONDEC *)
