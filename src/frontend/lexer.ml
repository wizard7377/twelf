Lexer  Stream' STREAM     LEXER  struct module (*! structure Paths = Paths' !*)
module type IdCase(* '<id>', currently unused *)
type Token(* string constants *)
exception let rec error(r,  , msg) raise (error (wrap (r,  , msg)))(* isSym (c) = B iff c is a legal symbolic identifier constituent *)
(* excludes quote character and digits, which are treated specially *)
(* Char.contains stages its computation *)
let  in(* isUFT8 (c) = assume that if a character is not ASCII it must be
     part of a UTF8 Unicode encoding.  Treat these as lowercase
     identifiers.  Somewhat of a hack until there is native Unicode
     string support. *)
let rec isUTF8(c) not (isAscii c)(* isQuote (c) = B iff c is the quote character *)
let rec isQuote(c) (c = ''')(* isIdChar (c) = B iff c is legal identifier constituent *)
let rec isIdChar(c) isLower (c) || isUpper (c) || isDigit (c) || isSym (c) || isQuote (c) || isUTF8 (c)(* stringToToken (idCase, string, region) = (token, region)
     converts special identifiers into tokens, returns ID token otherwise
  *)
let rec stringToToken(lower,  , "<-",  , r) (bACKARROW,  , r) stringToToken(lower,  , "->",  , r) (aRROW,  , r) stringToToken(upper,  , "_",  , r) (uNDERSCORE,  , r) stringToToken(lower,  , "=",  , r) (eQUAL,  , r) stringToToken(lower,  , "type",  , r) (tYPE,  , r) stringToToken(idCase,  , s,  , r) (iD (idCase,  , s),  , r)(* lex (inputFun) = (token, region) stream

     inputFun maintains state, reading input one line at a time and
     returning a string terminated by <newline> each time.
     The end of the stream is signalled by a string consisting only of ^D
     Argument to inputFun is the character position.
  *)
let rec lex(inputFun : Int -> String) let (* local state maintained by the lexer *)
let (* current string (line) *)
 (* position of first character in s *)
  in(* position after last character in s *)
let  in(* initialize line counter *)
(* neither lexer nor parser should ever try to look beyond EOF *)
let  in(* readNext () = ()
         Effect: read the next line, updating s, left, and right

         readNext relies on the invariant that identifiers are never
         spread across lines
      *)
let rec readNext() let let  inlet  in in if nextSize = 0(* end of file? *)
 then (s := eOFString; (* fake EOF character string *)
left := ! right; right := ! right + 1) else (s := nextLine; left := ! right; right := ! right + nextSize; newLine (! left))(* remember new line position *)
(* char (i) = character at position i
         Invariant: i >= !left
         Effects: will read input if i >= !right
      *)
let rec char(i) if i >= ! right then (readNext (); char (i)) else sub (! s,  , i - ! left)(* string (i,j) = substring at region including i, excluding j
         Invariant: i >= !left and i < j and j < !right
                    Note that the relevant parts must already have been read!
         Effects: None
      *)
let rec string(i,  , j) substring (! s,  , i - ! left,  , j - i)(* The remaining functions do not access the state or *)
(* stream directly, using only functions char and string *)
let rec idToToken(idCase,  , reg (i,  , j)) stringToToken (idCase,  , string (i,  , j),  , reg (i,  , j))(* Quote characters are part of the name *)
(* Treat quoted identifiers as lowercase, since they no longer *)
(* override infix state.  Quoted identifiers are now only used *)
(* inside pragmas *)
let rec qidToToken(reg (i,  , j)) (iD (lower,  , string (i,  , j + 1)),  , reg (i,  , j + 1))(* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).

       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
let rec lexInitial(':',  , i) (cOLON,  , reg (i - 1,  , i)) lexInitial('.',  , i) (dOT,  , reg (i - 1,  , i)) lexInitial('(',  , i) (lPAREN,  , reg (i - 1,  , i)) lexInitial(')',  , i) (rPAREN,  , reg (i - 1,  , i)) lexInitial('[',  , i) (lBRACKET,  , reg (i - 1,  , i)) lexInitial(']',  , i) (rBRACKET,  , reg (i - 1,  , i)) lexInitial('{',  , i) (lBRACE,  , reg (i - 1,  , i)) lexInitial('}',  , i) (rBRACE,  , reg (i - 1,  , i)) lexInitial('%',  , i) lexPercent (char (i),  , i + 1) lexInitial('_',  , i) lexID (upper,  , reg (i - 1,  , i)) lexInitial(''',  , i) lexID (lower,  , reg (i - 1,  , i)) lexInitial('\^D',  , i) (eOF,  , reg (i - 1,  , i - 1)) lexInitial('\"',  , i) lexString (reg (i - 1,  , i)) lexInitial(c,  , i) if isSpace (c) then lexInitial (char (i),  , i + 1) else if isUpper (c) then lexID (upper,  , reg (i - 1,  , i)) else if isDigit (c) then lexID (lower,  , reg (i - 1,  , i)) else if isLower (c) then lexID (lower,  , reg (i - 1,  , i)) else if isSym (c) then lexID (lower,  , reg (i - 1,  , i)) else if isUTF8 (c) then lexID (lower,  , reg (i - 1,  , i)) else error (reg (i - 1,  , i),  , "Illegal character " ^ toString (c))(* recover by ignoring: lexInitial (char(i), i+1) *)
 lexID(idCase,  , reg (i,  , j)) let let rec lexID'(j) if isIdChar (char (j)) then lexID' (j + 1) else idToToken (idCase,  , reg (i,  , j)) in lexID' (j)(* lexQUID is currently not used --- no quoted identifiers *)
 lexQUID(reg (i,  , j)) if isSpace (char (j)) then error (reg (i,  , j + 1),  , "Whitespace in quoted identifier")(* recover by adding implicit quote? *)
(* qidToToken (i, j) *)
 else if isQuote (char (j)) then qidToToken (reg (i,  , j)) else lexQUID (reg (i,  , j + 1)) lexPercent('.',  , i) (eOF,  , reg (i - 2,  , i)) lexPercent('{',  , i) lexPercentBrace (char (i),  , i + 1) lexPercent('%',  , i) lexComment ('%',  , i) lexPercent(c,  , i) if isIdChar (c) then lexPragmaKey (lexID (quoted,  , reg (i - 1,  , i))) else if isSpace (c) then lexComment (c,  , i) else error (reg (i - 1,  , i),  , "Comment character `%' not followed by white space") lexPragmaKey(iD (_,  , "infix"),  , r) (iNFIX,  , r) lexPragmaKey(iD (_,  , "prefix"),  , r) (pREFIX,  , r) lexPragmaKey(iD (_,  , "postfix"),  , r) (pOSTFIX,  , r) lexPragmaKey(iD (_,  , "mode"),  , r) (mODE,  , r) lexPragmaKey(iD (_,  , "unique"),  , r) (uNIQUE,  , r) lexPragmaKey(iD (_,  , "terminates"),  , r) (tERMINATES,  , r) lexPragmaKey(iD (_,  , "block"),  , r) (bLOCK,  , r) lexPragmaKey(iD (_,  , "worlds"),  , r) (wORLDS,  , r) lexPragmaKey(iD (_,  , "covers"),  , r) (cOVERS,  , r) lexPragmaKey(iD (_,  , "total"),  , r) (tOTAL,  , r) lexPragmaKey(iD (_,  , "reduces"),  , r) (rEDUCES,  , r) lexPragmaKey(iD (_,  , "tabled"),  , r) (tABLED,  , r) lexPragmaKey(iD (_,  , "keepTable"),  , r) (kEEPTABLE,  , r) lexPragmaKey(iD (_,  , "theorem"),  , r) (tHEOREM,  , r) lexPragmaKey(iD (_,  , "prove"),  , r) (pROVE,  , r) lexPragmaKey(iD (_,  , "establish"),  , r) (eSTABLISH,  , r) lexPragmaKey(iD (_,  , "assert"),  , r) (aSSERT,  , r) lexPragmaKey(iD (_,  , "abbrev"),  , r) (aBBREV,  , r) lexPragmaKey(iD (_,  , "name"),  , r) (nAME,  , r) lexPragmaKey(iD (_,  , "define"),  , r) (dEFINE,  , r) lexPragmaKey(iD (_,  , "solve"),  , r) (sOLVE,  , r) lexPragmaKey(iD (_,  , "query"),  , r) (qUERY,  , r) lexPragmaKey(iD (_,  , "fquery"),  , r) (fQUERY,  , r) lexPragmaKey(iD (_,  , "compile"),  , r) (cOMPILE,  , r) lexPragmaKey(iD (_,  , "querytabled"),  , r) (qUERYTABLED,  , r) lexPragmaKey(iD (_,  , "trustme"),  , r) (tRUSTME,  , r) lexPragmaKey(iD (_,  , "subord"),  , r) (sUBORD,  , r) lexPragmaKey(iD (_,  , "freeze"),  , r) (fREEZE,  , r) lexPragmaKey(iD (_,  , "thaw"),  , r) (tHAW,  , r) lexPragmaKey(iD (_,  , "deterministic"),  , r) (dETERMINISTIC,  , r) lexPragmaKey(iD (_,  , "clause"),  , r) (cLAUSE,  , r) lexPragmaKey(iD (_,  , "sig"),  , r) (sIG,  , r) lexPragmaKey(iD (_,  , "struct"),  , r) (sTRUCT,  , r) lexPragmaKey(iD (_,  , "where"),  , r) (wHERE,  , r) lexPragmaKey(iD (_,  , "include"),  , r) (iNCLUDE,  , r) lexPragmaKey(iD (_,  , "open"),  , r) (oPEN,  , r) lexPragmaKey(iD (_,  , "use"),  , r) (uSE,  , r) lexPragmaKey(iD (_,  , s),  , r) error (r,  , "Unknown keyword %" ^ s ^ " (single line comment starts with `%<whitespace>' or `%%')")(* comments are now started by %<whitespace> *)
(*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)
 lexComment('\n',  , i) lexInitial (char (i),  , i + 1) lexComment('%',  , i) lexCommentPercent (char (i),  , i + 1) lexComment('\^D',  , i) error (reg (i - 1,  , i - 1),  , "Unclosed single-line comment at end of file") lexComment(c,  , i) lexComment (char (i),  , i + 1) lexCommentPercent('.',  , i) (eOF,  , reg (i - 2,  , i)) lexCommentPercent(c,  , i) lexComment (c,  , i) lexPercentBrace(c,  , i) lexDComment (c,  , 1,  , i)(* functions lexing delimited comments below take nesting level l *)
 lexDComment('}',  , l,  , i) lexDCommentRBrace (char (i),  , l,  , i + 1) lexDComment('%',  , l,  , i) lexDCommentPercent (char (i),  , l,  , i + 1) lexDComment('\^D',  , l,  , i) error (reg (i - 1,  , i - 1),  , "Unclosed delimited comment at end of file") lexDComment(c,  , l,  , i) lexDComment (char (i),  , l,  , i + 1) lexDCommentPercent('{',  , l,  , i) lexDComment (char (i),  , l + 1,  , i + 1) lexDCommentPercent('.',  , l,  , i) error (reg (i - 2,  , i),  , "Unclosed delimited comment at end of file token `%.'") lexDCommentPercent(c,  , l,  , i) lexDComment (c,  , l,  , i) lexDCommentRBrace('%',  , 1,  , i) lexInitial (char (i),  , i + 1) lexDCommentRBrace('%',  , l,  , i) lexDComment (char (i),  , l - 1,  , i + 1) lexDCommentRBrace(c,  , l,  , i) lexDComment (c,  , l,  , i) lexString(reg (i,  , j)) (match char (j) with ('\"') -> (sTRING (string (i,  , j + 1)),  , reg (i,  , j + 1)) ('\n') -> error (reg (i - 1,  , i - 1),  , "Unclosed string constant at end of line")(* recover: (EOL, (i-1,i-1)) *)
 ('\^D') -> error (reg (i - 1,  , i - 1),  , "Unclosed string constant at end of file")(* recover: (EOF, (i-1,i-1)) *)
 _ -> lexString (reg (i,  , j + 1)))let rec lexContinue(j) delay (fun () -> lexContinue' (j)) lexContinue'(j) lexContinue'' (lexInitial (char (j),  , j + 1)) lexContinue''(mt as (iD _,  , reg (i,  , j))) cons (mt,  , lexContinueQualId (j)) lexContinue''(mt as (token,  , reg (i,  , j))) cons (mt,  , lexContinue (j)) lexContinueQualId(j) delay (fun () -> lexContinueQualId' (j)) lexContinueQualId'(j) if char (j) = '.' then if isIdChar (char (j + 1)) then cons ((pATHSEP,  , reg (j,  , j + 1)),  , lexContinue (j + 1)) else cons ((dOT,  , reg (j,  , j + 1)),  , lexContinue (j + 1)) else lexContinue' (j) in lexContinue (0)(* fun lex (inputFun) = let ... in ... end *)
let rec lexStream(instream) lex (fun i -> inputLine97 (instream))let rec lexTerminal(prompt0,  , prompt1) lex (fun 0 -> (print (prompt0); inputLine97 (stdIn)) i -> (print (prompt1); inputLine97 (stdIn)))let rec toString'(dOT) "." toString'(pATHSEP) "." toString'(cOLON) ":" toString'(lPAREN) "(" toString'(rPAREN) ")" toString'(lBRACKET) "[" toString'(rBRACKET) "]" toString'(lBRACE) "{" toString'(rBRACE) "}" toString'(bACKARROW) "<-" toString'(aRROW) "->" toString'(tYPE) "type" toString'(eQUAL) "=" toString'(uNDERSCORE) "_" toString'(iNFIX) "%infix" toString'(pREFIX) "%prefix" toString'(pOSTFIX) "%postfix" toString'(nAME) "%name" toString'(dEFINE) "%define" toString'(sOLVE) "%solve" toString'(qUERY) "%query" toString'(fQUERY) "%fquery" toString'(cOMPILE) "%compile" toString'(qUERYTABLED) "%querytabled" toString'(mODE) "%mode" toString'(uNIQUE) "%unique" toString'(cOVERS) "%covers" toString'(tOTAL) "%total" toString'(tERMINATES) "%terminates" toString'(bLOCK) "%block" toString'(wORLDS) "%worlds" toString'(rEDUCES) "%reduces" toString'(tABLED) "%tabled" toString'(kEEPTABLE) "%keepTable" toString'(tHEOREM) "%theorem" toString'(pROVE) "%prove" toString'(eSTABLISH) "%establish" toString'(aSSERT) "%assert" toString'(aBBREV) "%abbrev" toString'(tRUSTME) "%trustme" toString'(sUBORD) "%subord" toString'(fREEZE) "%freeze" toString'(tHAW) "%thaw" toString'(dETERMINISTIC) "%deterministic" toString'(cLAUSE) "%clause" toString'(sIG) "%sig" toString'(sTRUCT) "%struct" toString'(wHERE) "%where" toString'(iNCLUDE) "%include" toString'(oPEN) "%open" toString'(uSE) "%use"let rec toString(iD (_,  , s)) "identifier `" ^ s ^ "'" toString(eOF) "end of file or `%.'" toString(sTRING (s)) "constant string " ^ s toString(token) "`" ^ toString' token ^ "'"exception (* charToNat(c) = n converts character c to decimal equivalent *)
(* raises NotDigit(c) if c is not a digit 0-9 *)
let rec charToNat(c) let let  in in if digit < 0 || digit > 9 then raise (notDigit (c)) else digit(* stringToNat(s) = n converts string s to a natural number *)
(* raises NotDigit(c) if s contains character c which is not a digit *)
let rec stringToNat(s) let let  inlet rec stn(i,  , n) if i = l then n else stn (i + 1,  , 10 * n + charToNat (sub (s,  , i))) in stn (0,  , 0)(* isUpper (s) = true, if s is a string starting with an uppercase
     letter or underscore (_).
  *)
let rec isUpper("") false isUpper(s) let let  in in isUpper c || c = '_'(* local ... *)
end   module