(* Top-Level Parser *)

(* Author: Frank Pfenning *)

module Parser
    (Stream' : STREAM)
    (ExtSyn' : EXTSYN)
    (Names' : NAMES)
    (ExtConDec' : EXTCONDEC)
    (ExtQuery' : EXTQUERY)
    (ExtModes' : EXTMODES)
    (ThmExtSyn' : THMEXTSYN)
    (ModExtSyn' : MODEXTSYN)
    (ParseConDec : PARSE_CONDEC)
    (ParseQuery : PARSE_QUERY)
    (ParseFixity : PARSE_FIXITY)
    (ParseMode : PARSE_MODE)
    (ParseThm : PARSE_THM)
    (ParseModule : PARSE_MODULE)
    (ParseTerm : PARSE_TERM) : PARSER = struct
  (*! structure Parsing = Parsing' !*)

  module Stream = Stream'
  module ExtSyn = ExtSyn'
  module Names = Names'
  module ExtConDec = ExtConDec'
  module ExtQuery = ExtQuery'
  module ExtModes = ExtModes'
  module ThmExtSyn = ThmExtSyn'
  module ModExtSyn = ModExtSyn'

  type fileParseResult =
    | ConDec of ExtConDec.condec
    | FixDec of (Names.qid * Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.qid * Paths.region) * (string list * string list)
    | ModeDec of ExtModes.modedec list
    | UniqueDec of ExtModes.modedec list
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl
    | TabledDec of ThmExtSyn.tableddecl
    | KeepTableDec of ThmExtSyn.keepTabledecl
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert_ml
    | Query of int option * int option * ExtQuery.query
    | FQuery of ExtQuery.query
    | Compile of Names.qid list
    | Querytabled of int option * int option * ExtQuery.query
    | Solve of ExtQuery.define list * ExtQuery.solve
    | AbbrevDec of ExtConDec.condec
    | TrustMe of fileParseResult * Paths.region
    | SubordDec of Names.qid * Names.qid list
    | FreezeDec of Names.qid list
    | ThawDec of Names.qid list
    | DeterministicDec of Names.qid list
    | ClauseDec of ExtConDec.condec
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig
    | EndSubsig
    | Use of string
  (* Further pragmas to be added later here *)

  module L = Lexer
  module LS = LexerStream

  let rec stripDot = function
    | LS.Cons ((L.DOT, r), s) -> s
    | LS.Cons ((L.RPAREN, r), s) ->
        Parsing.error (r, "Unexpected right parenthesis")
    | LS.Cons ((L.RBRACE, r), s) -> Parsing.error (r, "Unexpected right brace")
    | LS.Cons ((L.RBRACKET, r), s) ->
        Parsing.error (r, "Unexpected right bracket")
    | LS.Cons ((L.EOF, r), s) -> Parsing.error (r, "Unexpected end of file")
    | LS.Cons ((L.Eq, r), s) -> Parsing.error (r, "Unexpected `='")
    | LS.Cons ((t, r), s) ->
        Parsing.error (r, "Expected `.', found " ^ L.toString t)
  (* Everything else should be impossible *)

  (*
    fun stripOptionalDot (LS.Cons ((L.DOT,r), s)) = s
      | stripOptionalDot f = LS.delay (fn () => f)
    *)

  let rec parseBound' = function
    | LS.Cons ((L.ID (_, "*"), r), s') -> (None, s')
    | LS.Cons ((L.ID (_, name), r), s') -> (
        try (Some (L.stringToNat name), s') with
        | Overflow -> Parsing.error (r, "Bound too large")
        | L.NotDigit _ ->
            Parsing.error
              (r, "Bound `" ^ name ^ "' neither `*' nor a natural number"))
    | LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected bound `*' or natural number, found " ^ L.toString t)
  (* pass theSigParser in order to be able to use
       this function polymorphically in the definition of parseStream *)

  let rec recParse (s, recparser, theSigParser, sc) =
    Stream.delay (fun () ->
        recParse' (LS.expose s, recparser, theSigParser, sc))

  and recParse' (f, recparser, theSigParser, sc) =
    match recparser f with
    | Parsing.Done x, f' -> sc (x, f')
    | Parsing.Continuation k, LS.Cons ((L.LBRACE, r1), s') ->
        let rec finish = function
          | LS.Cons ((L.RBRACE, r2), s'') ->
              Stream.Cons ((EndSubsig, r2), recParse (s'', k, theSigParser, sc))
          | LS.Cons ((t, r), _) ->
              Parsing.error (r, "Expected `}', found " ^ L.toString t)
        in
        Stream.Cons ((BeginSubsig, r1), theSigParser (s', finish))
    | Parsing.Continuation _, LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected `{', found " ^ L.toString t)

  let rec parseStream (s, sc) =
    Stream.delay (fun () -> parseStream' (LS.expose s, sc))

  and parseStream' = function
    | f, sc -> parseConDec' (f, sc)
    | f, sc -> parseAbbrev' (f, sc)
    | f, sc -> parseConDec' (f, sc)
    | f, sc -> parseFixity' (f, sc)
    | f, sc -> parseFixity' (f, sc)
    | f, sc -> parseFixity' (f, sc)
    | f, sc ->
        let namePref, f' = ParseFixity.parseNamePref' f in
        let r = Paths.join (r1, r2) in
        Stream.Cons ((NamePref namePref, r), parseStream (stripDot f', sc))
    | f, sc -> parseSolve' (f, sc)
    | f, sc -> parseSolve' (f, sc)
    | LS.Cons ((L.QUERY, r0), s'), sc ->
        let expected, s1 = parseBound' (LS.expose s') in
        let try_, s2 = parseBound' (LS.expose s1) in
        let query, f3 = ParseQuery.parseQuery' (LS.expose s2) in
        let r = Paths.join (r0, r') in
        Stream.Cons
          ((Query (expected, try_, query), r), parseStream (stripDot f3, sc))
    | LS.Cons ((L.FQUERY, r0), s'), sc ->
        let query, f3 = ParseQuery.parseQuery' (LS.expose s') in
        let r = Paths.join (r0, r') in
        Stream.Cons ((FQuery query, r), parseStream (stripDot f3, sc))
    | LS.Cons ((L.QUERYTABLED, r0), s'), sc ->
        let numSol, s1 = parseBound' (LS.expose s') in
        let try_, s2 = parseBound' (LS.expose s1) in
        let query, f3 = ParseQuery.parseQuery' (LS.expose s2) in
        let r = Paths.join (r0, r') in
        Stream.Cons
          ((Querytabled (numSol, try_, query), r), parseStream (stripDot f3, sc))
    | f, sc -> parseMode' (f, sc)
    | f, sc -> parseUnique' (f, sc)
    | f, sc -> parseCovers' (f, sc)
    | f, sc -> parseTotal' (f, sc)
    | f, sc -> parseTerminates' (f, sc)
    | f, sc -> parseConDec' (f, sc)
    | f, sc -> parseWorlds' (f, sc)
    | f, sc -> parseReduces' (f, sc)
    | f, sc -> parseTabled' (f, sc)
    | f, sc -> parseKeepTable' (f, sc)
    | f, sc -> parseTheorem' (f, sc)
    | f, sc -> parseProve' (f, sc)
    | f, sc -> parseEstablish' (f, sc)
    | f, sc -> parseAssert' (f, sc)
    | f, sc -> parseTrustMe' (f, sc)
    | f, sc -> parseFreeze' (f, sc)
    | f, sc -> parseSubord' (f, sc)
    | f, sc -> parseThaw' (f, sc)
    | f, sc -> parseDeterministic' (f, sc)
    | f, sc -> parseCompile' (f, sc)
    | f, sc -> parseClause' (f, sc)
    | f, sc -> parseSigDef' (f, sc)
    | f, sc -> parseStructDec' (f, sc)
    | f, sc -> parseInclude' (f, sc)
    | f, sc -> parseOpen' (f, sc)
    | f, sc -> parseUse' (LS.expose s', sc)
    | f, sc -> sc f
    | f, sc -> sc f
    | LS.Cons ((t, r), s'), sc ->
        Parsing.error
          (r, "Expected constant name or pragma keyword, found " ^ L.toString t)

  and parseConDec' (f, sc) =
    let conDec, f' = ParseConDec.parseConDec' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((ConDec conDec, r), parseStream (stripDot f', sc))

  and parseAbbrev' (f, sc) =
    let conDec, f' = ParseConDec.parseAbbrev' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((AbbrevDec conDec, r), parseStream (stripDot f', sc))

  and parseClause' (f, sc) =
    let conDec, f' = ParseConDec.parseClause' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((ClauseDec conDec, r), parseStream (stripDot f', sc))

  and parseFixity' (f, sc) =
    let fdec, f' = ParseFixity.parseFixity' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((FixDec fdec, r), parseStream (stripDot f', sc))

  and parseSolve' (f, sc) =
    let defnssolve, f' = ParseQuery.parseSolve' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((Solve defnssolve, r), parseStream (stripDot f', sc))

  and parseMode' (f, sc) =
    let mdecs, f' = ParseMode.parseMode' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((ModeDec mdecs, r), parseStream (stripDot f', sc))

  and parseUnique' (f, sc) =
    let mdecs, f' = ParseMode.parseMode' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((UniqueDec mdecs, r), parseStream (stripDot f', sc))

  and parseCovers' (f, sc) =
    let mdecs, f' = ParseMode.parseMode' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((CoversDec mdecs, r), parseStream (stripDot f', sc))

  and parseTotal' (f, sc) =
    let ldec, f' = ParseThm.parseTotal' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((TotalDec ldec, r), parseStream (stripDot f', sc))

  and parseTerminates' (f, sc) =
    let ldec, f' = ParseThm.parseTerminates' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((TerminatesDec ldec, r), parseStream (stripDot f', sc))

  and parseReduces' (f, sc) =
    let ldec, f' = ParseThm.parseReduces' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((ReducesDec ldec, r), parseStream (stripDot f', sc))

  and parseTabled' (f, sc) =
    let ldec, f' = ParseThm.parseTabled' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((TabledDec ldec, r), parseStream (stripDot f', sc))

  and parseKeepTable' (f, sc) =
    let ldec, f' = ParseThm.parseKeepTable' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((KeepTableDec ldec, r), parseStream (stripDot f', sc))

  and parseWorlds' (f, sc) =
    let ldec, f' = ParseThm.parseWorlds' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((WorldDec ldec, r), parseStream (stripDot f', sc))

  and parseTheorem' (f, sc) =
    let ldec, f' = ParseThm.parseTheoremDec' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((TheoremDec ldec, r), parseStream (stripDot f', sc))

  and parseProve' (f, sc) =
    let ldec, f' = ParseThm.parseProve' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((ProveDec ldec, r), parseStream (stripDot f', sc))

  and parseEstablish' (f, sc) =
    let ldec, f' = ParseThm.parseEstablish' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((EstablishDec ldec, r), parseStream (stripDot f', sc))

  and parseAssert' (f, sc) =
    let ldec, f' = ParseThm.parseAssert' f in
    let r = Paths.join (r0, r') in
    Stream.Cons ((AssertDec ldec, r), parseStream (stripDot f', sc))

  and parseTrustMe' (f, sc) =
    let rec parseNextDec' = function
      | Stream.Cons ((dec, r), s') -> Stream.Cons ((TrustMe (dec, r), r0), s')
      | Stream.Empty -> Parsing.error (r0, "No declaration after `%trustme'")
    in
    parseNextDec' (parseStream' (LS.expose s, sc))

  and parseSubord' (f, sc) =
    let qidpairs, f' = ParseTerm.parseSubord' (LS.expose s) in
    let r = Paths.join (r0, r') in
    let qidpairs =
      map (fun (qid1, qid2) -> (Names.Qid qid1, Names.Qid qid2)) qidpairs
    in
    Stream.Cons ((SubordDec qidpairs, r), parseStream (stripDot f', sc))

  and parseFreeze' (f, sc) =
    let qids, f' = ParseTerm.parseFreeze' (LS.expose s) in
    let r = Paths.join (r0, r') in
    let qids = map Names.Qid qids in
    Stream.Cons ((FreezeDec qids, r), parseStream (stripDot f', sc))

  and parseThaw' (f, sc) =
    let qids, f' = ParseTerm.parseThaw' (LS.expose s) in
    let r = Paths.join (r0, r') in
    let qids = map Names.Qid qids in
    Stream.Cons ((ThawDec qids, r), parseStream (stripDot f', sc))

  and parseDeterministic' (f, sc) =
    let qids, f' = ParseTerm.parseDeterministic' (LS.expose s) in
    let r = Paths.join (r0, r') in
    let qids = map Names.Qid qids in
    Stream.Cons ((DeterministicDec qids, r), parseStream (stripDot f', sc))

  and parseCompile' (f, sc) =
    let qids, f' = ParseTerm.parseCompile' (LS.expose s) in
    let r = Paths.join (r0, r') in
    let qids = map Names.Qid qids in
    Stream.Cons ((Compile qids, r), parseStream (stripDot f', sc))

  and parseSigDef' (f, sc) =
    let rec finish (sigdef, f') =
      Stream.Cons
        ((SigDef sigdef, Paths.join (r1, r2)), parseStream (stripDot f', sc))
    in
    recParse' (f, ParseModule.parseSigDef', parseStream, finish)

  and parseStructDec' (f, sc) =
    let rec finish (structdec, f') =
      Stream.Cons
        ( (StructDec structdec, Paths.join (r1, r2)),
          parseStream (stripDot f', sc) )
    in
    recParse' (f, ParseModule.parseStructDec', parseStream, finish)

  and parseInclude' (f, sc) =
    let rec finish (sigexp, f') =
      Stream.Cons
        ((Include sigexp, Paths.join (r1, r2)), parseStream (stripDot f', sc))
    in
    recParse' (f, ParseModule.parseInclude', parseStream, finish)

  and parseOpen' (f, sc) =
    let strexp, f' = ParseModule.parseOpen' f in
    Stream.Cons
      ((Open strexp, Paths.join (r1, r2)), parseStream (stripDot f', sc))

  and parseUse' = function
    | LS.Cons ((L.ID (_, name), r0), s), sc ->
        let f = LS.expose s in
        let r = Paths.join (r0, r') in
        Stream.Cons ((Use name, r), parseStream (stripDot f, sc))
    | LS.Cons ((_, r), _), sc ->
        Parsing.error (r, "Constraint solver name expected")

  let rec parseQ s = Stream.delay (fun () -> parseQ' (LS.expose s))

  and parseQ' f =
    let query, f' = ParseQuery.parseQuery' f in
    Stream.Cons (query, parseQ (stripDot f'))

  let rec parseTLStream instream =
    let rec finish = function
      | LS.Cons ((L.EOF, r), s) -> Stream.Empty
      | LS.Cons ((L.RBRACE, r), s) -> Parsing.error (r, "Unmatched `}'")
    in
    parseStream (L.lexStream instream, finish)

  let parseStream = parseTLStream
  let rec parseTerminalQ prompts = parseQ (L.lexTerminal prompts)
  (* local ... in *)
end

(* functor Parser *)
