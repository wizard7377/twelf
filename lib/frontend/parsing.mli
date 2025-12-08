(* General basis for parsing modules *)
(* Author: Frank Pfenning *)

module type PARSING =
sig
  module Stream : STREAM
  (*
  module Lexer : LEXER
    sharing Lexer.Stream = Stream
  *)

  type lexResult = Lexer.Token * Paths.region

  type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  (* recursive parser (allows parsing functions that need to parse
     a module type expression to temporarily suspend themselves) *)
  type 'a RecParseResult =
    Done of 'a
  | Continuation of 'a RecParseResult parser

  type 'a recparser = 'a RecParseResult parser

  (* useful combinator for recursive parsers *)
  val recwith : 'a recparser * ('a -> 'b) -> 'b recparser

  exception Error of string
  val error : Paths.region * string -> 'a	(* always raises Error *)
end;; (* module type PARSING *)
