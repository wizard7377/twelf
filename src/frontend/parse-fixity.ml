ParseFixity  Names' NAMES     PARSE_FIXITY  struct (*! structure Parsing = Parsing' !*)
module (* some shorthands *)
module module module let rec fixToString(strength (p)) toString p(* idToPrec (region, (idCase, name)) = n
       where n is the precedence indicated by name, which should consists
       of all digits.  Raises error otherwise, or if precedence it too large
    *)
let rec idToPrec(r,  , (_,  , name)) let let  in in if less (prec,  , minPrec) || less (maxPrec,  , prec) then error (r,  , "Precedence out of range [" ^ fixToString minPrec ^ "," ^ fixToString maxPrec ^ "]") else prec(*-----------------------------*)
(* Parsing fixity declarations *)
(*-----------------------------*)
(* parseFixCon "id" *)
let rec parseFixCon(fixity,  , cons ((iD (_,  , name),  , r),  , s')) (((qid (nil,  , name),  , r),  , fixity),  , expose s') parseFixCon(fixity,  , cons ((t,  , r),  , s')) error (r,  , "Expected identifier to assign fixity, found " ^ toString t)(* parseFixPrec "n id" where n is precedence *)
let rec parseFixPrec(fixity,  , cons ((iD id,  , r),  , s')) parseFixCon (fixity (idToPrec (r,  , id)),  , expose s') parseFixPrec(fixity,  , cons ((t,  , r),  , s')) error (r,  , "Expected precedence, found " ^ toString t)(* parseInfix "none|left|right n id" where n is precedence *)
let rec parseInfix(cons ((iD (lower,  , "none"),  , r),  , s')) parseFixPrec ((fun p -> infix (p,  , none)),  , expose s') parseInfix(cons ((iD (lower,  , "left"),  , r),  , s')) parseFixPrec ((fun p -> infix (p,  , left)),  , expose s') parseInfix(cons ((iD (lower,  , "right"),  , r),  , s')) parseFixPrec ((fun p -> infix (p,  , right)),  , expose s') parseInfix(cons ((t,  , r),  , s')) error (r,  , "Expected associatitivy `left', `right', or `none', found " ^ toString t)(* parsePrefix "n id" where n is precedence *)
let rec parsePrefix(f) parseFixPrec (prefix,  , f)(* parsePostfix "n id" where n is precedence *)
let rec parsePostfix(f) parseFixPrec (postfix,  , f)(* parseFixity' : lexResult stream -> (name,fixity) * lexResult stream
       Invariant: token stream starts with %infix, %prefix or %postfix
    *)
let rec parseFixity'(cons ((iNFIX,  , r),  , s')) parseInfix (expose s') parseFixity'(cons ((pREFIX,  , r),  , s')) parsePrefix (expose s') parseFixity'(cons ((pOSTFIX,  , r),  , s')) parsePostfix (expose s')(* anything else should be impossible *)
let rec parseFixity(s) parseFixity' (expose (s))(*------------------------------------*)
(* Parsing name preferences %name ... *)
(*------------------------------------*)
(* parseName5 "string ... )" or ")" *)
let rec parseName5(name,  , r0,  , prefENames,  , prefUNames,  , cons ((iD (_,  , prefUName),  , r),  , s')) parseName5 (name,  , r0,  , prefENames,  , prefUNames @ [prefUName],  , expose s') parseName5(name,  , r0,  , prefENames,  , prefUNames,  , cons ((rPAREN,  , r),  , s')) (((qid (nil,  , name),  , r0),  , (prefENames,  , prefUNames)),  , expose s') parseName5(name,  , r0,  , prefENames,  , prefUNames,  , cons ((t,  , r),  , s')) error (r,  , "Expected name preference or ')', found " ^ toString t)(* parseName3 "string" or "" *)
let rec parseName3(name,  , r0,  , prefEName,  , cons ((iD (_,  , prefUName),  , r),  , s')) (((qid (nil,  , name),  , r0),  , (prefEName,  , [prefUName])),  , expose s') parseName3(name,  , r0,  , prefEName,  , cons ((lPAREN,  , r),  , s')) parseName5 (name,  , r0,  , prefEName,  , nil,  , expose s') parseName3(name,  , r0,  , prefEName,  , f) (((qid (nil,  , name),  , r0),  , (prefEName,  , nil)),  , f)(* parseName4 "string ... )" or ")" *)
let rec parseName4(name,  , r0,  , prefENames,  , cons ((iD (_,  , prefEName),  , r),  , s')) if isUpper prefEName then parseName4 (name,  , r0,  , prefENames @ [prefEName],  , expose s') else error (r,  , "Expected uppercase identifer, found " ^ prefEName) parseName4(name,  , r0,  , prefENames,  , cons ((rPAREN,  , r),  , s')) parseName3 (name,  , r0,  , prefENames,  , expose s') parseName4(name,  , r0,  , prefENames,  , cons ((t,  , r),  , s')) error (r,  , "Expected name preference or ')', found " ^ toString t)(* parseName2 "string" or "string string"
              or "(string ... ) string"  or " string (string ...)"
              or "(string ... ) (string ...)" *)
let rec parseName2(name,  , r0,  , cons ((iD (_,  , prefEName),  , r),  , s')) if isUpper prefEName then parseName3 (name,  , r0,  , [prefEName],  , expose s') else error (r,  , "Expected uppercase identifer, found " ^ prefEName) parseName2(name,  , r0,  , cons ((lPAREN,  , r),  , s')) parseName4 (name,  , r0,  , nil,  , expose s') parseName2(name,  , r0,  , cons ((t,  , r),  , s')) error (r,  , "Expected name preference, found " ^ toString t)(* parseName1 "id string" or "id string string" *)
let rec parseName1(cons ((iD (_,  , name),  , r),  , s')) parseName2 (name,  , r,  , expose s') parseName1(cons ((t,  , r),  , s')) error (r,  , "Expected identifer to assign name preference, found " ^ toString t)(* parseNamePref' "%name id string" or "%name id string string"
       Invariant: token stream starts with %name
    *)
let rec parseNamePref'(cons ((nAME,  , r),  , s')) parseName1 (expose s')let rec parseNamePref(s) parseNamePref' (expose s)let  inlet  in(* local ... in *)
end