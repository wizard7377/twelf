(* The Parser *)
(* Author: Richard Fontana *)

module Parse  (module DextSyn  : DEXTSYN)
   (Interface : INTERFACE)
   (module Parserr : PARSERR
                     sharing type Parserr.arg = Interface.arg
                     sharing type Parserr.pos = Interface.pos
                     sharing type Parserr.result = DextSyn.Ast
                module Tokens : Delphin_TOKENS
                     sharing type Tokens.token = Parserr.Token.token
                     sharing type Tokens.svalue = Parserr.svalue) : PARSE =

struct

module DextSyn = DextSyn
module Interface = Interface
module Parserr = Parserr
module Tokens = Tokens
module Streamm = Parserr.Streamm
module Token = Parserr.Token

(* Given a lexer, invoke parser *)
let rec invoke lexstream =
   Parserr.parse(0, lexstream, Interface.error, Interface.nothing)

(* Parse a named input file *)
let rec fparse fname =
   let let _ = Interface.init_line ()
       let infile = TextIO.openIn(fname)
       let lexer = Parserr.makeLexer
           (fun _ -> Compat.inputLine97 infile)
       let empty = !Interface.line
       let dummyEOF = Tokens.EOF(empty, empty)
       fun loop lexer =
           let let (result, lexer) = invoke lexer
               let (nextToken, lexer) = Parserr.Streamm.get lexer
           in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then ()
              else loop lexer;
              (* DextSyn.printAst result; *)
              (* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
             (* DextSyn.termparse result; *)
              ()
           end
   in loop lexer
   end


let rec sparse () =
  let
    let _ = Interface.init_line ()
    let infile = TextIO.openString (TextIO.input TextIO.stdIn)
    let lexer = Parserr.makeLexer
           (fun _ -> Compat.inputLine97 infile)
    let empty = !Interface.line
    let dummyEOF = Tokens.EOF(empty, empty)
    fun loop lexer =
      let let (result, lexer) = invoke lexer
          let (nextToken, lexer) = Parserr.Streamm.get lexer
       in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then (* () *)
                    result
              else loop lexer
       end
   in loop lexer
   end




let rec  gparse fname =
   let let _ = Interface.init_line ()
       let infile = TextIO.openIn(fname)
       let lexer = Parserr.makeLexer
           (fun _ -> Compat.inputLine97 infile)
       let empty = !Interface.line
       let dummyEOF = Tokens.EOF(empty, empty)
       fun loop lexer =
           let let (result, lexer) = invoke lexer
               let (nextToken, lexer) = Parserr.Streamm.get lexer
           in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then (* () *)
                    result
              else loop lexer
              (* DextSyn.printAst result; *)
              (* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
             (* DextSyn.termparse result; *)
           (*   ()  *)
           end
   in loop lexer
   end
end  (* functor Parse *)


