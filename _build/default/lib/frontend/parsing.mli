(* General basis for parsing modules *)
(* Author: Frank Pfenning *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PARSING =
sig
  structure Stream : STREAM
  (*
  structure Lexer : LEXER
    sharing Lexer.Stream = Stream
  *)

  type lex_result = Lexer.token * Paths.region

  type 'a parser = lex_result Stream.front -> 'a * lex_result Stream.front

  (* recursive parser (allows parsing functions that need to parse
     a signature expression to temporarily suspend themselves) *)
  datatype 'a rec_parse_result =
    Done of 'a
  | Continuation of 'a rec_parse_result parser

  type 'a recparser = 'a rec_parse_result parser

  (* useful combinator for recursive parsers *)
  val recwith : 'a recparser * ('a -> 'b) -> 'b recparser

  exception Error of string
  val error : Paths.region * string -> 'a	(* always raises Error *)
end (* GEN END SIGNATURE DECLARATION *);  (* signature PARSING *)
