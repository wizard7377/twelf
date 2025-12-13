(* Lexer *)
(* Author: Frank Pfenning *)
(* Modified: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) Lexer (structure Stream' : STREAM
               (*! structure Paths' : PATHS !*)
                 )
  : LEXER =
struct

  structure Stream = Stream'
  (*! structure Paths = Paths' !*)

  local
    structure P = Paths
  in

  datatype id_case =
      Upper                             (* [A-Z]<id> or _<id> *)
    | Lower                             (* any other <id> *)
    | Quoted                            (* '<id>', currently unused *)

  datatype token =
      EOF                               (* end of file or stream, also `%.' *)
    | DOT                               (* `.' *)
    | PATHSEP                           (* `.' between <id>s *)
    | COLON                             (* `:' *)
    | LPAREN | RPAREN                   (* `(' `)' *)
    | LBRACKET | RBRACKET               (* `[' `]' *)
    | LBRACE | RBRACE                   (* `{' `}' *)
    | BACKARROW | ARROW                 (* `<-' `->' *)
    | TYPE                              (* `type' *)
    | EQUAL                             (* `=' *)
    | ID of id_case * string             (* identifer *)
    | UNDERSCORE                        (* `_' *)
    | INFIX | PREFIX | POSTFIX          (* `%infix' `%prefix' `%postfix' *)
    | NAME                              (* `%name' *)
    | DEFINE                            (* `%define' *) (* -rv 8/27/01 *)
    | SOLVE                             (* `%solve' *)
    | QUERY                             (* `%query' *)
    | FQUERY                            (* `%fquery' *)
    | COMPILE                           (* '%compile' *) (* -ABP 4/4/03 *)
    | QUERYTABLED                       (* `%querytabled *)
    | MODE                              (* `%mode' *)
    | UNIQUE                            (* `%unique' *) (* -fp 8/17/03 *)
    | COVERS                            (* `%covers' *) (* -fp 3/7/01 *)
    | TOTAL                             (* `%total' *) (* -fp 3/18/01 *)
    | TERMINATES                        (* `%terminates' *)
    | REDUCES                           (* `%reduces' *) (* -bp  6/05/99 *)
    | TABLED                            (* `%tabled' *)     (* -bp 11/20/01 *)
    | KEEPTABLE                         (* `%keepTable' *)  (* -bp 11/20/01 *)
    | THEOREM                           (* `%theorem' *)
    | BLOCK                             (* `%block' *) (* -cs 5/29/01 *)
    | WORLDS                            (* `%worlds' *)
    | PROVE                             (* `%prove' *)
    | ESTABLISH                         (* `%establish' *)
    | ASSERT                            (* `%assert' *)
    | ABBREV                            (* `%abbrev' *)
    | TRUSTME                           (* `%trustme' *) (* -fp 8/26/05 *)
    | FREEZE                            (* `%freeze' *)
    | THAW                              (* `%thaw' *)
    | SUBORD                            (* `%subord' *) (* -gaw 07/11/08 *)
    | DETERMINISTIC                     (* `%deterministic' *) (* -rv 11/27/01 *)
    | CLAUSE                            (* `%clause' *) (* -fp 8/9/02 *)
    | SIG                               (* `%sig' *)
    | STRUCT                            (* `%struct' *)
    | WHERE                             (* `%where' *)
    | INCLUDE                           (* `%include' *)
    | OPEN                              (* `%open' *)
    | USE                               (* `%use' *)
    | STRING of string                  (* string constants *)

  exception Error of string

  fun error (r, msg) = raise Error (P.wrap (r, msg))

  (* isSym (c) = B iff c is a legal symbolic identifier constituent *)
  (* excludes quote character and digits, which are treated specially *)
  (* Char.contains stages its computation *)
  (* GEN BEGIN TAG OUTSIDE LET *) val isSym : char -> bool = Char.contains "_!&$^+/<=>?@~|#*`;,-\\" (* GEN END TAG OUTSIDE LET *)

  (* isUFT8 (c) = assume that if a character is not ASCII it must be
     part of a UTF8 Unicode encoding.  Treat these as lowercase
     identifiers.  Somewhat of a hack until there is native Unicode
     string support. *)
  fun isUTF8 (c) = not (Char.isAscii c)

  (* isQuote (c) = B iff c is the quote character *)
  fun isQuote (c) = (c = #"'")

  (* isIdChar (c) = B iff c is legal identifier constituent *)
  fun isIdChar (c) = Char.isLower(c) orelse Char.isUpper (c)
                     orelse Char.isDigit (c) orelse isSym(c)
                     orelse isQuote (c) orelse isUTF8(c)

  (* stringToToken (idCase, string, region) = (token, region)
     converts special identifiers into tokens, returns ID token otherwise
  *)
  fun (* GEN BEGIN FUN FIRST *) stringToToken (Lower, "<-", r) = (BACKARROW, r) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) stringToToken (Lower, "->", r) = (ARROW, r) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) stringToToken (Upper, "_", r) = (UNDERSCORE, r) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) stringToToken (Lower, "=", r) = (EQUAL, r) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) stringToToken (Lower, "type", r) = (TYPE, r) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) stringToToken (idCase, s, r) = (ID(idCase,s), r) (* GEN END FUN BRANCH *)

  (* lex (inputFun) = (token, region) stream

     inputFun maintains state, reading input one line at a time and
     returning a string terminated by <newline> each time.
     The end of the stream is signalled by a string consisting only of ^D
     Argument to inputFun is the character position.
  *)
  fun lex (inputFun:int -> string) =
  let
    local (* local state maintained by the lexer *)
      (* GEN BEGIN TAG OUTSIDE LET *) val s = ref ""                    (* current string (line) *)
      and left = ref 0                  (* position of first character in s *)
      and right = ref 0 (* GEN END TAG OUTSIDE LET *)                 (* position after last character in s *)
      (* GEN BEGIN TAG OUTSIDE LET *) val _ = P.resetLines () (* GEN END TAG OUTSIDE LET *)           (* initialize line counter *)
  
      (* neither lexer nor parser should ever try to look beyond EOF *)
      (* GEN BEGIN TAG OUTSIDE LET *) val EOFString = String.str #"\^D" (* GEN END TAG OUTSIDE LET *)
  
      (* readNext () = ()
         Effect: read the next line, updating s, left, and right
  
         readNext relies on the invariant that identifiers are never
         spread across lines
      *)
      fun readNext () =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val nextLine = inputFun (!right) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val nextSize = String.size (nextLine) (* GEN END TAG OUTSIDE LET *)
          in
            if nextSize = 0             (* end of file? *)
              then (s := EOFString;     (* fake EOF character string *)
                    left := !right;
                    right := !right + 1)
            else (s := nextLine;
                  left := !right;
                  right := !right + nextSize;
                  P.newLine (!left)) (* remember new line position *)
          end
    in
      (* char (i) = character at position i
         Invariant: i >= !left
         Effects: will read input if i >= !right
      *)
      fun char (i) =
          if i >= !right then (readNext (); char (i))
          else String.sub (!s, i - !left)
  
      (* string (i,j) = substring at region including i, excluding j
         Invariant: i >= !left and i < j and j < !right
                    Note that the relevant parts must already have been read!
         Effects: None
      *)
      fun string (i,j) = String.substring (!s, i - !left, j-i)
    end
  
    (* The remaining functions do not access the state or *)
    (* stream directly, using only functions char and string *)
  
    fun idToToken (idCase, P.Reg (i,j)) = stringToToken (idCase, string (i,j), P.Reg (i,j))
  
    (* Quote characters are part of the name *)
    (* Treat quoted identifiers as lowercase, since they no longer *)
    (* override infix state.  Quoted identifiers are now only used *)
    (* inside pragmas *)
    fun qidToToken (P.Reg (i,j)) = (ID(Lower, string(i,j+1)), P.Reg (i,j+1))
  
    (* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).
  
       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
    fun (* GEN BEGIN FUN FIRST *) lexInitial (#":", i) = (COLON, P.Reg (i-1,i)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#".", i) = (DOT, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"(", i) = (LPAREN, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#")", i) = (RPAREN, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"[", i) = (LBRACKET, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"]", i) = (RBRACKET, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"{", i) = (LBRACE, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"}", i) = (RBRACE, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"%", i) = lexPercent (char(i), i+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"_", i) = lexID (Upper, P.Reg (i-1,i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"'", i) = lexID (Lower, P.Reg (i-1,i)) (* GEN END FUN BRANCH *) (* lexQUID (i-1,i) *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"\^D", i) = (EOF, P.Reg (i-1,i-1)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (#"\"", i) = lexString (P.Reg(i-1, i)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexInitial (c, i) =
        if Char.isSpace (c) then lexInitial (char (i),i+1)
        else if Char.isUpper(c) then lexID (Upper, P.Reg (i-1,i))
        else if Char.isDigit(c) then lexID (Lower, P.Reg (i-1,i))
        else if Char.isLower(c) then lexID (Lower, P.Reg (i-1,i))
        else if isSym(c) then lexID (Lower, P.Reg (i-1,i))
        else if isUTF8(c) then lexID (Lower, P.Reg (i-1,i))
        else error (P.Reg (i-1,i), "Illegal character " ^ Char.toString (c)) (* GEN END FUN BRANCH *)
        (* recover by ignoring: lexInitial (char(i), i+1) *)
  
    and lexID (idCase, P.Reg (i,j)) =
        let fun lexID' (j) =
                if isIdChar (char(j)) then lexID' (j+1)
                else
                   idToToken (idCase, P.Reg (i,j))
        in
          lexID' (j)
        end
  
    (* lexQUID is currently not used --- no quoted identifiers *)
    and lexQUID (P.Reg (i,j)) =
        if Char.isSpace (char(j))
          then error (P.Reg (i,j+1), "Whitespace in quoted identifier")
               (* recover by adding implicit quote? *)
               (* qidToToken (i, j) *)
        else if isQuote (char(j)) then qidToToken (P.Reg (i,j))
             else lexQUID (P.Reg (i, j+1))
  
    and (* GEN BEGIN FUN FIRST *) lexPercent (#".", i) = (EOF, P.Reg (i-2,i)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexPercent (#"{", i) = lexPercentBrace (char(i), i+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPercent (#"%", i) = lexComment (#"%", i) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPercent (c, i) =
        if isIdChar(c) then lexPragmaKey (lexID (Quoted, P.Reg (i-1, i)))
        else if Char.isSpace(c) then lexComment (c, i)
          else error (P.Reg (i-1, i), "Comment character `%' not followed by white space") (* GEN END FUN BRANCH *)
  
    and (* GEN BEGIN FUN FIRST *) lexPragmaKey (ID(_, "infix"), r) = (INFIX, r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "prefix"), r) = (PREFIX, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "postfix"), r) = (POSTFIX, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "mode"), r) = (MODE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "unique"), r) = (UNIQUE, r) (* GEN END FUN BRANCH *) (* -fp 8/17/03 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "terminates"), r) = (TERMINATES, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "block"), r) = (BLOCK, r) (* GEN END FUN BRANCH *) (* -cs 6/3/01 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "worlds"), r) = (WORLDS, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "covers"), r) = (COVERS, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "total"), r) = (TOTAL, r) (* GEN END FUN BRANCH *) (* -fp 3/18/01 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "reduces"), r) = (REDUCES, r) (* GEN END FUN BRANCH *)         (* -bp 6/5/99 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "tabled"), r) = (TABLED, r) (* GEN END FUN BRANCH *)           (* -bp 20/11/01 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "keepTable"), r) = (KEEPTABLE, r) (* GEN END FUN BRANCH *)     (* -bp 20/11/04 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "theorem"), r) = (THEOREM, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "prove"), r) = (PROVE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "establish"), r) = (ESTABLISH, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "assert"), r) = (ASSERT, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "abbrev"), r) = (ABBREV, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "name"), r) = (NAME, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "define"), r) = (DEFINE, r) (* GEN END FUN BRANCH *) (* -rv 8/27/01 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "solve"), r) = (SOLVE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "query"), r) = (QUERY, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "fquery"), r) = (FQUERY, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "compile"), r) = (COMPILE, r) (* GEN END FUN BRANCH *) (* -ABP 4/4/03 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "querytabled"), r) = (QUERYTABLED, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "trustme"), r) = (TRUSTME, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "subord"), r) = (SUBORD, r) (* GEN END FUN BRANCH *) (* -gaw 07/11/08 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "freeze"), r) = (FREEZE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "thaw"), r) = (THAW, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "deterministic"), r) = (DETERMINISTIC, r) (* GEN END FUN BRANCH *) (* -rv 11/27/01 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "clause"), r) = (CLAUSE, r) (* GEN END FUN BRANCH *) (* -fp 08/09/02 *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "sig"), r) = (SIG, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "struct"), r) = (STRUCT, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "where"), r) = (WHERE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "include"), r) = (INCLUDE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "open"), r) = (OPEN, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, "use"), r) = (USE, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexPragmaKey (ID(_, s), r) =
        error (r, "Unknown keyword %" ^ s ^ " (single line comment starts with `%<whitespace>' or `%%')") (* GEN END FUN BRANCH *)
      (* comments are now started by %<whitespace> *)
      (*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)
  
    and (* GEN BEGIN FUN FIRST *) lexComment (#"\n", i) = lexInitial (char(i), i+1) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexComment (#"%", i) = lexCommentPercent (char(i), i+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexComment (#"\^D", i) =
          error (P.Reg (i-1, i-1), "Unclosed single-line comment at end of file") (* GEN END FUN BRANCH *)
          (* recover: (EOF, (i-1,i-1)) *)
      | (* GEN BEGIN FUN BRANCH *) lexComment (c, i) = lexComment (char(i), i+1) (* GEN END FUN BRANCH *)
  
    and (* GEN BEGIN FUN FIRST *) lexCommentPercent (#".", i) = (EOF, P.Reg (i-2, i)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexCommentPercent (c, i) = lexComment (c, i) (* GEN END FUN BRANCH *)
  
    and lexPercentBrace (c, i) = lexDComment (c, 1, i)
  
    (* functions lexing delimited comments below take nesting level l *)
    and (* GEN BEGIN FUN FIRST *) lexDComment (#"}", l, i) = lexDCommentRBrace (char(i), l, i+1) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexDComment (#"%", l, i) = lexDCommentPercent (char(i), l, i+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexDComment (#"\^D", l, i) =
          (* pass comment beginning for error message? *)
          error (P.Reg (i-1,i-1), "Unclosed delimited comment at end of file") (* GEN END FUN BRANCH *)
          (* recover: (EOF, (i-1,i-1)) *)
      | (* GEN BEGIN FUN BRANCH *) lexDComment (c, l, i) = lexDComment (char(i), l, i+1) (* GEN END FUN BRANCH *)
  
    and (* GEN BEGIN FUN FIRST *) lexDCommentPercent (#"{", l, i) = lexDComment (char(i), l+1, i+1) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexDCommentPercent (#".", l, i) =
          error (P.Reg (i-2, i), "Unclosed delimited comment at end of file token `%.'") (* GEN END FUN BRANCH *)
          (* recover: (EOF, (i-2,i)) *)
      | (* GEN BEGIN FUN BRANCH *) lexDCommentPercent (c, l, i) = lexDComment (c, l, i) (* GEN END FUN BRANCH *)
  
    and (* GEN BEGIN FUN FIRST *) lexDCommentRBrace (#"%", 1, i) = lexInitial (char(i), i+1) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexDCommentRBrace (#"%", l, i) = lexDComment (char(i), l-1, i+1) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) lexDCommentRBrace (c, l, i) = lexDComment (c, l, i) (* GEN END FUN BRANCH *)
  
    and lexString (P.Reg(i, j)) =
          (case char(j)
             of (#"\"") => (STRING (string (i, j+1)), P.Reg(i, j+1))
              | (#"\n") =>
                  error (P.Reg (i-1, i-1), "Unclosed string constant at end of line")
                  (* recover: (EOL, (i-1,i-1)) *)
              | (#"\^D") =>
                  error (P.Reg (i-1, i-1), "Unclosed string constant at end of file")
                  (* recover: (EOF, (i-1,i-1)) *)
              | _ => lexString (P.Reg(i, j+1)))
  
    fun lexContinue (j) = Stream.delay ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => lexContinue' (j) (* GEN END FUNCTION EXPRESSION *))
    and lexContinue' (j) = lexContinue'' (lexInitial (char(j), j+1))
  
    and (* GEN BEGIN FUN FIRST *) lexContinue'' (mt as (ID _, P.Reg (i,j))) =
          Stream.Cons (mt, lexContinueQualId (j)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) lexContinue'' (mt as (token, P.Reg (i,j))) =
          Stream.Cons (mt, lexContinue (j)) (* GEN END FUN BRANCH *)
  
    and lexContinueQualId (j) =
          Stream.delay ((* GEN BEGIN FUNCTION EXPRESSION *) fn () => lexContinueQualId' (j) (* GEN END FUNCTION EXPRESSION *))
    and lexContinueQualId' (j) =
          if char (j) = #"."
            then if isIdChar (char (j+1))
                   then Stream.Cons ((PATHSEP, P.Reg (j,j+1)), lexContinue (j+1))
                 else Stream.Cons ((DOT, P.Reg (j,j+1)), lexContinue (j+1))
          else lexContinue' (j)
  
  in
    lexContinue (0)
  end  (* fun lex (inputFun) = let ... in ... end *)

  fun lexStream (instream) = lex ((* GEN BEGIN FUNCTION EXPRESSION *) fn i => Compat.inputLine97 (instream) (* GEN END FUNCTION EXPRESSION *))

  fun lexTerminal (prompt0, prompt1) =
        lex ((* GEN BEGIN FUNCTION EXPRESSION *) fn 0 => (print (prompt0) ;
                      Compat.inputLine97 (TextIO.stdIn))
              | i => (print (prompt1) ;
                      Compat.inputLine97 (TextIO.stdIn)) (* GEN END FUNCTION EXPRESSION *))

  fun (* GEN BEGIN FUN FIRST *) toString' (DOT) = "." (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) toString' (PATHSEP) = "." (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (COLON) = ":" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (LPAREN) = "(" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (RPAREN) = ")" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (LBRACKET) = "[" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (RBRACKET) = "]" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (LBRACE) = "{" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (RBRACE) = "}" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (BACKARROW) = "<-" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (ARROW) = "->" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (TYPE) = "type" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (EQUAL) = "=" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (UNDERSCORE) = "_" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (INFIX) = "%infix" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (PREFIX) = "%prefix" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (POSTFIX) = "%postfix" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (NAME) = "%name" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (DEFINE) = "%define" (* GEN END FUN BRANCH *)    (* -rv 8/27/01 *)
    | (* GEN BEGIN FUN BRANCH *) toString' (SOLVE) = "%solve" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (QUERY) = "%query" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (FQUERY) = "%fquery" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (COMPILE) = "%compile" (* GEN END FUN BRANCH *)  (* -ABP 4/4/03 *)
    | (* GEN BEGIN FUN BRANCH *) toString' (QUERYTABLED) = "%querytabled" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (MODE) = "%mode" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (UNIQUE) = "%unique" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (COVERS) = "%covers" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (TOTAL) = "%total" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (TERMINATES) = "%terminates" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (BLOCK) = "%block" (* GEN END FUN BRANCH *)      (* -cs 6/3/01. *)
    | (* GEN BEGIN FUN BRANCH *) toString' (WORLDS) = "%worlds" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (REDUCES) = "%reduces" (* GEN END FUN BRANCH *)              (*  -bp 6/5/99. *)
    | (* GEN BEGIN FUN BRANCH *) toString' (TABLED) = "%tabled" (* GEN END FUN BRANCH *)                (*  -bp 20/11/01. *)
    | (* GEN BEGIN FUN BRANCH *) toString' (KEEPTABLE) = "%keepTable" (* GEN END FUN BRANCH *)          (*  -bp 04/11/03. *)
    | (* GEN BEGIN FUN BRANCH *) toString' (THEOREM) = "%theorem" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (PROVE) = "%prove" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (ESTABLISH) = "%establish" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (ASSERT) = "%assert" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (ABBREV) = "%abbrev" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (TRUSTME) = "%trustme" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (SUBORD) = "%subord" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (FREEZE) = "%freeze" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (THAW) = "%thaw" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (DETERMINISTIC) = "%deterministic" (* GEN END FUN BRANCH *)  (* -rv 11/27/01. *)
    | (* GEN BEGIN FUN BRANCH *) toString' (CLAUSE) = "%clause" (* GEN END FUN BRANCH *) (* -fp 08/09/02 *)
    | (* GEN BEGIN FUN BRANCH *) toString' (SIG) = "%sig" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (STRUCT) = "%struct" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (WHERE) = "%where" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (INCLUDE) = "%include" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (OPEN) = "%open" (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) toString' (USE) = "%use" (* GEN END FUN BRANCH *)

 fun (* GEN BEGIN FUN FIRST *) toString (ID(_,s)) = "identifier `" ^ s ^ "'" (* GEN END FUN FIRST *)
   | (* GEN BEGIN FUN BRANCH *) toString (EOF) = "end of file or `%.'" (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) toString (STRING(s)) = "constant string " ^ s (* GEN END FUN BRANCH *)
   | (* GEN BEGIN FUN BRANCH *) toString (token) = "`" ^ toString' token ^ "'" (* GEN END FUN BRANCH *)

 exception NotDigit of char

 (* charToNat(c) = n converts character c to decimal equivalent *)
 (* raises NotDigit(c) if c is not a digit 0-9 *)
 fun charToNat (c) =
     let (* GEN BEGIN TAG OUTSIDE LET *) val digit = Char.ord(c) - Char.ord(#"0") (* GEN END TAG OUTSIDE LET *)
     in
       if digit < 0 orelse digit > 9
         then raise NotDigit (c)
       else digit
     end

 (* stringToNat(s) = n converts string s to a natural number *)
 (* raises NotDigit(c) if s contains character c which is not a digit *)
 fun stringToNat (s) =
     let (* GEN BEGIN TAG OUTSIDE LET *) val l = String.size s (* GEN END TAG OUTSIDE LET *)
         fun stn (i, n) =
             if i = l then n
             else stn (i+1, 10 * n + charToNat (String.sub (s, i)))
     in
       stn (0, 0)
     end

  (* isUpper (s) = true, if s is a string starting with an uppercase
     letter or underscore (_).
  *)
  fun (* GEN BEGIN FUN FIRST *) isUpper ("") = false (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) isUpper (s) =
      let (* GEN BEGIN TAG OUTSIDE LET *) val c = String.sub (s, 0) (* GEN END TAG OUTSIDE LET *)
       in
         Char.isUpper c orelse c = #"_"
      end (* GEN END FUN BRANCH *)

  end  (* local ... *)

end (* GEN END FUNCTOR DECL *);  (* functor Lexer *)

structure Lexer =
  Lexer (structure Stream' = Stream
         (*! structure Paths' = Paths !*)
           );
