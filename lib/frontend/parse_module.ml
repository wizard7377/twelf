open Basis

(* Parsing modules *)

(* Author: Kevin Watkins *)

module type PARSE_MODULE = sig
  (*! structure Parsing : Parsing.PARSING !*)
  module ModExtSyn : Recon_module.MODEXTSYN

  (* val parseSigExp' : ModExtSyn.sigexp Parsing.recparser *)
  val parseSigDef' : ModExtSyn.sigdef Parsing.recparser

  (* val parseStructExp' : ModExtSyn.strexp Parsing.parser *)
  val parseStructDec' : ModExtSyn.structdec Parsing.recparser
  val parseInclude' : ModExtSyn.sigexp Parsing.recparser
  val parseOpen' : ModExtSyn.strexp Parsing.parser
end
(* Parsing modules *)

(* Author: Kevin Watkins *)

module ParseModule
    (ModExtSyn' : Recon_module.MODEXTSYN)
    (ParseTerm : Parse_prg.Parse_term.PARSE_TERM) : Parse_prg.PARSE_MODULE =
struct
  (*! structure Parsing = Parsing' !*)

  module ModExtSyn = ModExtSyn'
  module L = Lexer
  module LS = LexerStream
  module E = ModExtSyn

  let rec parseStructExp' = function
    | f ->
        let (ids, (L.ID (_, id), r1)), f' = ParseTerm.parseQualId' f in
        (E.strexp (ids, id, Paths.join (r0, r1)), f')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected structure identifier, found token " ^ L.toString t)

  let rec parseColonEqual' = function
    | LS.Cons ((L.COLON, r1), s') -> (
        match LS.expose s' with
        | LS.Cons ((L.Eq, _), s'') -> ((), LS.expose s'')
        | LS.Cons ((t, r2), s'') ->
            Parsing.error (r2, "Expected `=', found token " ^ L.toString t))
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `:=', found token " ^ L.toString t)

  let rec parseDot' = function
    | LS.Cons ((L.DOT, r), s') -> (r, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `.', found token " ^ L.toString t)

  let rec parseConInst' = function
    | f ->
        let (ids, (L.ID (_, id), r1)), f1 = ParseTerm.parseQualId' f in
        let _, f2 = parseColonEqual' f1 in
        let tm, f3 = ParseTerm.parseTerm' f2 in
        let r2, f4 = parseDot' f3 in
        (E.coninst ((ids, id, Paths.join (r0, r1)), tm, Paths.join (r0, r2)), f4)
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  let rec parseStrInst2' = function
    | r0, f ->
        let (ids, (L.ID (_, id), r2)), f1 = ParseTerm.parseQualId' f in
        let _, f2 = parseColonEqual' f1 in
        let strexp, f3 = parseStructExp' f2 in
        let r3, f4 = parseDot' f3 in
        ( E.strinst ((ids, id, Paths.join (r1, r2)), strexp, Paths.join (r0, r3)),
          f4 )
    | r0, LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected structure identifier, found token " ^ L.toString t)

  let rec parseStrInst' = function
    | LS.Cons ((L.STRUCT, r), s') -> parseStrInst2' (r, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `%struct', found token " ^ L.toString t)

  let rec parseInsts' = function
    | f ->
        let inst, f' = parseConInst' f in
        let insts, f'' = parseInsts' f' in
        (inst :: insts, f'')
    | f ->
        let inst, f' = parseStrInst' f in
        let insts, f'' = parseInsts' f' in
        (inst :: insts, f'')
    | LS.Cons ((L.RBRACE, _), s') -> ([], LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected identifier or `%struct', found token " ^ L.toString t)

  let rec parseInstantiate' = function
    | f -> parseInsts' (LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  let rec parseWhereClauses' = function
    | f, sigexp ->
        let insts, f' = parseInstantiate' (LS.expose s') in
        parseWhereClauses' (f', E.wheresig (sigexp, insts))
    | f, sigexp -> (sigexp, f)

  let rec parseSigExp' = function
    | LS.Cons ((L.ID (_, id), r), s) ->
        let sigexp, f' = parseWhereClauses' (LS.expose s, E.sigid (id, r)) in
        (Parsing.Done sigexp, f')
    | f ->
        ( Parsing.Continuation
            (fun f' ->
              let sigexp, f'' = parseWhereClauses' (f', E.thesig) in
              (Parsing.Done sigexp, f'')),
          f )
    | LS.Cons ((t, r), _) ->
        Parsing.error
          ( r,
            "Expected signature name or expression, found token " ^ L.toString t
          )

  let rec parseSgEqual' = function
    | idOpt, LS.Cons ((L.Eq, r), s') ->
        Parsing.recwith
          (parseSigExp', fun sigexp -> E.sigdef (idOpt, sigexp))
          (LS.expose s')
    | idOpt, LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `=', found token " ^ L.toString t)

  let rec parseSgDef' = function
    | LS.Cons ((L.ID (_, id), r), s') -> parseSgEqual' (Some id, LS.expose s')
    | LS.Cons ((L.UNDERSCORE, r), s') -> parseSgEqual' (None, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected signature identifier, found token " ^ L.toString t)

  let rec parseSigDef' (LS.Cons ((L.SIG, r), s')) = parseSgDef' (LS.expose s')

  let rec parseStrDec2' = function
    | idOpt, LS.Cons ((L.COLON, r), s') ->
        Parsing.recwith
          (parseSigExp', fun sigexp -> E.structdec (idOpt, sigexp))
          (LS.expose s')
    | idOpt, LS.Cons ((L.Eq, r), s') ->
        let strexp, f' = parseStructExp' (LS.expose s') in
        (Parsing.Done (E.structdef (idOpt, strexp)), f')
    | idOpt, LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t)

  let rec parseStrDec' = function
    | LS.Cons ((L.ID (_, id), r), s') -> parseStrDec2' (Some id, LS.expose s')
    | LS.Cons ((L.UNDERSCORE, r), s') -> parseStrDec2' (None, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected structure identifier, found token " ^ L.toString t)

  let rec parseStructDec' (LS.Cons ((L.STRUCT, r), s')) =
    parseStrDec' (LS.expose s')

  let rec parseInclude' (LS.Cons ((L.INCLUDE, r), s')) =
    parseSigExp' (LS.expose s')

  let rec parseOpen' (LS.Cons ((L.OPEN, r), s')) =
    parseStructExp' (LS.expose s')
end
