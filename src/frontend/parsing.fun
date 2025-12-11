functor Parsing
  (structure Stream' : STREAM
   (*! structure Lexer' : LEXER !*)
   (*! sharing Lexer'.Stream = Stream' !*)
     )
     : PARSING =
struct

  structure Stream = Stream'
  (*! structure Lexer = Lexer' !*)

  type lex_result = Lexer.token * Paths.region

  type 'a parser = lex_result Stream.front -> 'a * lex_result Stream.front

  datatype 'a rec_parse_result =
    Done of 'a
  | Continuation of 'a rec_parse_result parser

  type 'a recparser = 'a rec_parse_result parser

  fun recwith (recparser, func) f =
      (case recparser f
         of (Done x, f') => (Done (func x), f')
          | (Continuation k, f') => (Continuation (recwith (k, func)), f'))

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

end;  (* functor Parsing *)

structure Parsing =
  Parsing (structure Stream' = Stream
           (*! structure Lexer' = Lexer !*)
             );
