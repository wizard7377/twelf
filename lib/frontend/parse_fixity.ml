open Basis

(* Parsing Fixity Declarations *)

(* Author: Frank Pfenning *)

module type PARSE_FIXITY = sig
  (*! structure Parsing : Parsing.PARSING !*)
  module Names : Names.NAMES

  val parseFixity' :
    (Names.qid * Paths.region) * Names.Fixity.fixity Parsing.parser

  val parseNamePref' :
    (Names.qid * Paths.region) * (string list * string list) Parsing.parser
end

(* signature Parse_prg.PARSE_FIXITY *)
(* Parsing Fixity and Name Preference Declarations *)

(* Author: Frank Pfenning *)

module ParseFixity (Names' : Names.NAMES) : Parse_prg.PARSE_FIXITY = struct
  (*! structure Parsing = Parsing' !*)

  module Names = Names'
  (* some shorthands *)

  module L = Lexer
  module LS = LexerStream
  module FX = NamesFixity

  let rec fixToString (FX.Strength p) = Int.toString p
  (* idToPrec (region, (idCase, name)) = n
       where n is the precedence indicated by name, which should consists
       of all digits.  Raises error otherwise, or if precedence it too large
    *)

  let rec idToPrec (r, (_, name)) =
    let prec =
      try FX.Strength (L.stringToNat name) with
      | Overflow -> Parsing.error (r, "Precedence too large")
      | L.NotDigit _ -> Parsing.error (r, "Precedence not a natural number")
    in
    if FX.less (prec, FX.minPrec) || FX.less (FX.maxPrec, prec) then
      Parsing.error
        ( r,
          "Precedence out of range [" ^ fixToString FX.minPrec ^ ","
          ^ fixToString FX.maxPrec ^ "]" )
    else prec
  (*-----------------------------*)

  (* Parsing fixity declarations *)

  (*-----------------------------*)

  (* parseFixCon "id" *)

  let rec parseFixCon = function
    | fixity, LS.Cons ((L.ID (_, name), r), s') ->
        (((Names.Qid ([], name), r), fixity), LS.expose s')
    | fixity, LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected identifier to assign fixity, found " ^ L.toString t)
  (* parseFixPrec "n id" where n is precedence *)

  let rec parseFixPrec = function
    | fixity, LS.Cons ((L.ID id, r), s') ->
        parseFixCon (fixity (idToPrec (r, id)), LS.expose s')
    | fixity, LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected precedence, found " ^ L.toString t)
  (* parseInfix "none|left|right n id" where n is precedence *)

  let rec parseInfix = function
    | LS.Cons ((L.ID (L.Lower, "none"), r), s') ->
        parseFixPrec ((fun p -> FX.Infix (p, FX.None)), LS.expose s')
    | LS.Cons ((L.ID (L.Lower, "left"), r), s') ->
        parseFixPrec ((fun p -> FX.Infix (p, FX.Left)), LS.expose s')
    | LS.Cons ((L.ID (L.Lower, "right"), r), s') ->
        parseFixPrec ((fun p -> FX.Infix (p, FX.Right)), LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          ( r,
            "Expected associatitivy `left', `right', or `none', found "
            ^ L.toString t )
  (* parsePrefix "n id" where n is precedence *)

  let rec parsePrefix f = parseFixPrec (FX.Prefix, f)
  (* parsePostfix "n id" where n is precedence *)

  let rec parsePostfix f = parseFixPrec (FX.Postfix, f)
  (* parseFixity' : lexResult stream -> (name,fixity) * lexResult stream
       Invariant: token stream starts with %infix, %prefix or %postfix
    *)

  let rec parseFixity' = function
    | LS.Cons ((L.INFIX, r), s') -> parseInfix (LS.expose s')
    | LS.Cons ((L.PREFIX, r), s') -> parsePrefix (LS.expose s')
    | LS.Cons ((L.POSTFIX, r), s') -> parsePostfix (LS.expose s')
  (* anything else should be impossible *)

  let rec parseFixity s = parseFixity' (LS.expose s)
  (*------------------------------------*)

  (* Parsing name preferences %name ... *)

  (*------------------------------------*)

  (* parseName5 "string ... )" or ")" *)

  let rec parseName5 = function
    | name, r0, prefENames, prefUNames, LS.Cons ((L.ID (_, prefUName), r), s')
      ->
        parseName5
          (name, r0, prefENames, prefUNames @ [ prefUName ], LS.expose s')
    | name, r0, prefENames, prefUNames, LS.Cons ((L.RPAREN, r), s') ->
        (((Names.Qid ([], name), r0), (prefENames, prefUNames)), LS.expose s')
    | name, r0, prefENames, prefUNames, LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected name preference or ')', found " ^ L.toString t)
  (* parseName3 "string" or "" *)

  let rec parseName3 = function
    | name, r0, prefEName, LS.Cons ((L.ID (_, prefUName), r), s') ->
        (((Names.Qid ([], name), r0), (prefEName, [ prefUName ])), LS.expose s')
    | name, r0, prefEName, LS.Cons ((L.LPAREN, r), s') ->
        parseName5 (name, r0, prefEName, [], LS.expose s')
    | name, r0, prefEName, f ->
        (((Names.Qid ([], name), r0), (prefEName, [])), f)
  (* parseName4 "string ... )" or ")" *)

  let rec parseName4 = function
    | name, r0, prefENames, LS.Cons ((L.ID (_, prefEName), r), s') ->
        if L.isUpper prefEName then
          parseName4 (name, r0, prefENames @ [ prefEName ], LS.expose s')
        else
          Parsing.error (r, "Expected uppercase identifer, found " ^ prefEName)
    | name, r0, prefENames, LS.Cons ((L.RPAREN, r), s') ->
        parseName3 (name, r0, prefENames, LS.expose s')
    | name, r0, prefENames, LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected name preference or ')', found " ^ L.toString t)
  (* parseName2 "string" or "string string"
              or "(string ... ) string"  or " string (string ...)"
              or "(string ... ) (string ...)" *)

  let rec parseName2 = function
    | name, r0, LS.Cons ((L.ID (_, prefEName), r), s') ->
        if L.isUpper prefEName then
          parseName3 (name, r0, [ prefEName ], LS.expose s')
        else
          Parsing.error (r, "Expected uppercase identifer, found " ^ prefEName)
    | name, r0, LS.Cons ((L.LPAREN, r), s') ->
        parseName4 (name, r0, [], LS.expose s')
    | name, r0, LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected name preference, found " ^ L.toString t)
  (* parseName1 "id string" or "id string string" *)

  let rec parseName1 = function
    | LS.Cons ((L.ID (_, name), r), s') -> parseName2 (name, r, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          ( r,
            "Expected identifer to assign name preference, found "
            ^ L.toString t )
  (* parseNamePref' "%name id string" or "%name id string string"
       Invariant: token stream starts with %name
    *)

  let rec parseNamePref' (LS.Cons ((L.NAME, r), s')) = parseName1 (LS.expose s')
  let rec parseNamePref s = parseNamePref' (LS.expose s)
  let parseFixity' = parseFixity'
  let parseNamePref' = parseNamePref'
  (* local ... in *)
end

(* functor ParseFixity *)
