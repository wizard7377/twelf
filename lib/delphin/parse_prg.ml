(* The Parser *)
(* Author: Richard Fontana *)

functor (* GEN BEGIN FUNCTOR DECL *) Parse  (structure DextSyn  : DEXTSYN
                structure Interface : INTERFACE
                structure Parserr : PARSERR
                     sharing type Parserr.arg = Interface.arg
                     sharing type Parserr.pos = Interface.pos
                     sharing type Parserr.result = DextSyn.ast
                structure Tokens : Delphin_TOKENS
                     sharing type Tokens.token = Parserr.Token.token
                     sharing type Tokens.svalue = Parserr.svalue) : PARSE =

struct

structure DextSyn = DextSyn
structure Interface = Interface
structure Parserr = Parserr
structure Tokens = Tokens
structure Streamm = Parserr.Streamm
structure Token = Parserr.Token

(* Given a lexer, invoke parser *)
fun invoke lexstream =
   Parserr.parse(0, lexstream, Interface.error, Interface.nothing)

(* Parse a named input file *)
fun fparse fname =
   let (* GEN BEGIN TAG OUTSIDE LET *) val _ = Interface.init_line () (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val infile = TextIO.openIn(fname) (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val lexer = Parserr.makeLexer
           ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Compat.inputLine97 infile (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val empty = !Interface.line (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val dummyEOF = Tokens.EOF(empty, empty) (* GEN END TAG OUTSIDE LET *)
       fun loop lexer =
           let (* GEN BEGIN TAG OUTSIDE LET *) val (result, lexer) = invoke lexer (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (nextToken, lexer) = Parserr.Streamm.get lexer (* GEN END TAG OUTSIDE LET *)
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


fun sparse () =
  let
    (* GEN BEGIN TAG OUTSIDE LET *) val _ = Interface.init_line () (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val infile = TextIO.openString (TextIO.input TextIO.stdIn) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lexer = Parserr.makeLexer
           ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Compat.inputLine97 infile (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val empty = !Interface.line (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val dummyEOF = Tokens.EOF(empty, empty) (* GEN END TAG OUTSIDE LET *)
    fun loop lexer =
      let (* GEN BEGIN TAG OUTSIDE LET *) val (result, lexer) = invoke lexer (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (nextToken, lexer) = Parserr.Streamm.get lexer (* GEN END TAG OUTSIDE LET *)
       in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then (* () *)
                    result
              else loop lexer
       end
   in loop lexer
   end




fun  gparse fname =
   let (* GEN BEGIN TAG OUTSIDE LET *) val _ = Interface.init_line () (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val infile = TextIO.openIn(fname) (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val lexer = Parserr.makeLexer
           ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Compat.inputLine97 infile (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val empty = !Interface.line (* GEN END TAG OUTSIDE LET *)
       (* GEN BEGIN TAG OUTSIDE LET *) val dummyEOF = Tokens.EOF(empty, empty) (* GEN END TAG OUTSIDE LET *)
       fun loop lexer =
           let (* GEN BEGIN TAG OUTSIDE LET *) val (result, lexer) = invoke lexer (* GEN END TAG OUTSIDE LET *)
               (* GEN BEGIN TAG OUTSIDE LET *) val (nextToken, lexer) = Parserr.Streamm.get lexer (* GEN END TAG OUTSIDE LET *)
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
end (* GEN END FUNCTOR DECL *)  (* functor Parse *)


