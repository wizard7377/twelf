module Parsing (Stream' : STREAM) : PARSING = struct module Stream = Stream'
(*! structure Lexer = Lexer' !*)

type lexResult = Lexer.token * Paths.region
type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front
type 'a recParseResult = Done of 'a | Continuation of 'a recParseResult parser
type 'a recparser = 'a recParseResult parser
let rec recwith (recparser, func) f  = (match recparser f with (Done x, f') -> (Done (func x), f') | (Continuation k, f') -> (Continuation (recwith (k, func)), f'))
exception Error of string
let rec error (r, msg)  = raise (Error (Paths.wrap (r, msg)))
 end


(* functor Parsing *)


module Parsing = Parsing (struct module Stream' = Stream end)

