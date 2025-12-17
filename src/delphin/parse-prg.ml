Parse  DextSyn DEXTSYN    Interface INTERFACE    Parserr PARSERR     Arg Arg   Pos Pos   Result Ast  Tokens Delphin_TOKENS     Token Token   Svalue Svalue   PARSE  struct module module module module module module (* Given a lexer, invoke parser *)
let rec invokelexstream parse (0,  , lexstream,  , error,  , nothing)(* Parse a named input file *)
let rec fparsefname let let  inlet  inlet  inlet  inlet  inlet rec looplexer let let  inlet  in in if sameToken (nextToken,  , dummyEOF) then () else loop lexer(* DextSyn.printAst result; *)
(* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
(* DextSyn.termparse result; *)
() in loop lexerlet rec sparse() let let  inlet  inlet  inlet  inlet  inlet rec looplexer let let  inlet  in in if sameToken (nextToken,  , dummyEOF) then (* () *)
result else loop lexer in loop lexerlet rec gparsefname let let  inlet  inlet  inlet  inlet  inlet rec looplexer let let  inlet  in in if sameToken (nextToken,  , dummyEOF) then (* () *)
result else loop lexer(* DextSyn.printAst result; *)
(* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
(* DextSyn.termparse result; *)
(*   ()  *)
 in loop lexerend