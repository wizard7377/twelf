module Parsing
  (module Stream' : STREAM): PARSING =
   (*! module Lexer' : LEXER !*)
   (*! sharing Lexer'.Stream = Stream' !*)
struct

  module Stream = Stream'
  (*! module Lexer = Lexer' !*)

  type lexresult = Lexer.Token * Paths.region

  type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  type 'a RecParseResult =
    Done of 'a
  | Continuation of 'a RecParseResult parser

  type 'a recparser = 'a RecParseResult parser

  let rec recwith (recparser, func) f =
      (case recparser f
         of (Done x, f') => (Done (func x), f')
          | (Continuation k, f') => (Continuation (recwith (k, func)), f'))

  exception Error of string
  let rec error (r, msg) = raise Error (Paths.wrap (r, msg))

end;; (* functor Parsing *)

module Parsing =
  Parsing (module Stream' = Stream
           (*! module Lexer' = Lexer !*)
             );
