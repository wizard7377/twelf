(* Parsing Signature Entries *)

(* Author: Frank Pfenning *)

module type PARSE_CONDEC = sig
  (*! structure Parsing : Parsing.PARSING !*)
  module ExtConDec : Recon_condec.EXTCONDEC

  val parseConDec' : ExtConDec.condec Parsing.parser
  val parseAbbrev' : ExtConDec.condec Parsing.parser
  val parseClause' : ExtConDec.condec Parsing.parser
end

(* signature Parse_prg.PARSE_CONDEC *)
(* Parsing Signature Entries *)

(* Author: Frank Pfenning *)

module ParseConDec (ExtConDec' : Recon_condec.EXTCONDEC) (ParseTerm : Parse_prg.Parse_term.PARSE_TERM) :
  Parse_prg.PARSE_CONDEC = struct
  (*! structure Parsing = Parsing' !*)

  module ExtConDec = ExtConDec'
  module L = Lexer
  module LS = LexerStream
  (* parseConDec3  "U" *)

  let rec parseConDec3 (optName, optTm, s) =
    let tm', f' = ParseTerm.parseTerm' (LS.expose s) in
    (ExtConDec.condef (optName, tm', optTm), f')
  (* parseConDec2  "= U" | "" *)

  let rec parseConDec2 = function
    | optName, (tm, LS.Cons ((L.Eq, r), s')) ->
        parseConDec3 (optName, Some tm, s')
    | Some name, (tm, f) -> (ExtConDec.condec (name, tm), f)
    | None, (tm, LS.Cons ((t, r), s')) ->
        Parsing.error (r, "Illegal anonymous declared constant")
  (* parseConDec1  ": V = U" | "= U" *)

  let rec parseConDec1 = function
    | optName, LS.Cons ((L.COLON, r), s') ->
        parseConDec2 (optName, ParseTerm.parseTerm' (LS.expose s'))
    | optName, LS.Cons ((L.Eq, r), s') -> parseConDec3 (optName, None, s')
    | optName, LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)
  (* BlockDec parser *)

  let rec parseBlock = function
    | LS.Cons ((L.ID (_, "block"), r), s') -> ParseTerm.parseCtx' (LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `block', found " ^ L.toString t)

  let rec parseSome = function
    | name, LS.Cons ((L.ID (_, "some"), r), s') ->
        let g1, f' = ParseTerm.parseCtx' (LS.expose s') in
        let g2, f'' = parseBlock f' in
        (ExtConDec.blockdec (name, g1, g2), f'')
    | name, f ->
        let g2, f' = parseBlock f in
        (ExtConDec.blockdec (name, [], g2), f')
    | name, LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `some' or `block', found " ^ L.toString t)

  let rec parseBlockDec1 = function
    | name, LS.Cons ((L.COLON, r), s') -> parseSome (name, LS.expose s')
    | name, LS.Cons ((L.Eq, r), s') ->
        let g, f = ParseTerm.parseQualIds' (LS.expose s') in
        (ExtConDec.blockdef (name, g), f)
    | name, LS.Cons ((t, r), s') ->
        Parsing.error (r, "`:' expected, found token " ^ L.toString t)

  let rec parseBlockDec' = function
    | LS.Cons ((L.ID (idCase, name), r), s') ->
        parseBlockDec1 (name, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Label identifier expected, found token " ^ L.toString t)
  (* parseConDec' : lexResult front -> ExtConDec.ConDec * lexResult front
       Invariant: first token in exposed input stream is an identifier or underscore
    *)

  let rec parseConDec' = function
    | LS.Cons ((L.ID (idCase, name), r), s') ->
        parseConDec1 (Some name, LS.expose s')
    | LS.Cons ((L.UNDERSCORE, r), s') -> parseConDec1 (None, LS.expose s')
    | LS.Cons ((L.BLOCK, r), s') -> parseBlockDec' (LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          ( r,
            "Constant or block declaration expected, found token "
            ^ L.toString t )
  (* parseConDec --- currently not exported *)

  let rec parseConDec s = parseConDec' (LS.expose s)
  let rec parseAbbrev' (LS.Cons ((L.ABBREV, r), s)) = parseConDec s
  let rec parseClause' (LS.Cons ((L.CLAUSE, r), s)) = parseConDec s
  (* -fp *)

  let parseConDec' = parseConDec'
  let parseAbbrev' = parseAbbrev'
  let parseClause' = parseClause'
  (* local ... in *)
end

(* functor ParseConDec *)
