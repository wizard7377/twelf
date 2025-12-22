(* Lexer *)

(* Author: Frank Pfenning *)

module type LEXER = sig
  (* Stream is not memoizing for_sml efficiency *)
  module Stream : STREAM

  (*! structure Paths : PATHS !*)
  type idCase = Upper | Lower | Quoted

  (* '<id>', currently unused *)
  type token =
    | EOF
    | DOT
    | PATHSEP
    | COLON
    | LPAREN
    | RPAREN
    | LBRACKET
    | RBRACKET
    | LBRACE
    | RBRACE
    | BACKARROW
    | ARROW
    | TYPE
    | Eq
    | ID of idCase * string
    | UNDERSCORE
    | INFIX
    | PREFIX
    | POSTFIX
    | NAME
    | DEFINE
    | SOLVE
    | QUERY
    | FQUERY
    | COMPILE
    | QUERYTABLED
    | MODE
    | UNIQUE
    | COVERS
    | TOTAL
    | TERMINATES
    | BLOCK
    | WORLDS
    | REDUCES
    | TABLED
    | KEEPTABLE
    | THEOREM
    | PROVE
    | ESTABLISH
    | ASSERT
    | ABBREV
    | TRUSTME
    | FREEZE
    | THAW
    | SUBORD
    | DETERMINISTIC
    | CLAUSE
    | SIG
    | STRUCT
    | WHERE
    | INCLUDE
    | OPEN
    | USE
    | STRING of string

  (* string constants *)
  exception Error of string

  (* lexer returns an infinite stream, terminated by EOF token *)
  val lexStream : TextIO.instream -> token * Paths.region Stream.stream
  val lexTerminal : string * string -> token * Paths.region Stream.stream
  val toString : token -> string

  (* Utilities *)
  exception NotDigit of char

  val stringToNat : string -> int
  val isUpper : string -> bool
end

(* signature LEXER *)
