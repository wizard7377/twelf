(* Parsing modules *)
(* Author: Kevin Watkins *)

module ParseModule
  ((*! module Paths : PATHS !*)
   (*! module Parsing' : PARSING !*)
   (*! sharing Parsing'.Lexer.Paths = Paths !*)
   module ModExtSyn' : MODEXTSYN
   (*! sharing ModExtSyn'.Paths = Paths !*)
   module ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ModExtSyn'.ExtSyn)
  : PARSE_MODULE =
struct

  (*! module Parsing = Parsing' !*)
  module ModExtSyn = ModExtSyn'

  module L = Lexer
  module LS = Lexer.Stream
  module E = ModExtSyn

  fun parseStructExp' (f as LS.Cons ((L.ID _, r0), _)) =
      let
        let ((ids, (L.ID (_, id), r1)), f') = ParseTerm.parseQualId' f
      in
        (E.strexp (ids, id, Paths.join (r0, r1)), f')
      end
    | parseStructExp' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected module identifier, found token " ^ L.toString t)

  fun parseColonEqual' (LS.Cons ((L.COLON, r1), s')) =
      (case LS.expose s'
         of LS.Cons ((L.EQUAL, _), s'') => ((), LS.expose s'')
          | LS.Cons ((t, r2), s'') =>
              Parsing.error (r2, "Expected `=', found token " ^ L.toString t))
    | parseColonEqual' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `:=', found token " ^ L.toString t)

  fun parseDot' (LS.Cons ((L.DOT, r), s')) = (r, LS.expose s')
    | parseDot' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `.', found token " ^ L.toString t)

  fun parseConInst' (f as LS.Cons ((L.ID _, r0), _)) =
      let
        let ((ids, (L.ID (_, id), r1)), f1) = ParseTerm.parseQualId' (f)
        let (_, f2) = parseColonEqual' (f1)
        let (tm, f3) = ParseTerm.parseTerm' (f2)
        let (r2, f4) = parseDot' (f3)
      in
        (E.coninst ((ids, id, Paths.join (r0, r1)), tm, Paths.join (r0, r2)),
         f4)
      end
    | parseConInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  fun parseStrInst2' (r0, f as LS.Cons ((L.ID _, r1), _)) =
      let
        let ((ids, (L.ID (_, id), r2)), f1) = ParseTerm.parseQualId' (f)
        let (_, f2) = parseColonEqual' (f1)
        let (strexp, f3) = parseStructExp' (f2)
        let (r3, f4) = parseDot' (f3)
      in
        (E.strinst ((ids, id, Paths.join (r1, r2)),
                    strexp, Paths.join (r0, r3)),
         f4)
      end
    | parseStrInst2' (r0, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected module identifier, found token " ^ L.toString t)

  fun parseStrInst' (LS.Cons ((L.STRUCT, r), s')) =
        parseStrInst2' (r, LS.expose s')
    | parseStrInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `%struct', found token " ^ L.toString t)

  fun parseInsts' (f as LS.Cons ((L.ID _, _), _)) =
      let
        let (inst, f') = parseConInst' (f)
        let (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (f as LS.Cons ((L.STRUCT, _), _)) =
      let
        let (inst, f') = parseStrInst' (f)
        let (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (LS.Cons ((L.RBRACE, _), s')) =
        (nil, LS.expose s')
    | parseInsts' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier or `%struct', found token " ^ L.toString t)

  fun parseInstantiate' (f as LS.Cons ((L.LBRACE, _), s')) =
        parseInsts' (LS.expose s')
    | parseInstantiate' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  fun parseWhereClauses' (f as LS.Cons ((L.WHERE, _), s'), sigexp) =
      let
        let (insts, f') = parseInstantiate' (LS.expose s')
      in
        parseWhereClauses' (f', E.wheresig (sigexp, insts))
      end
    | parseWhereClauses' (f, sigexp) = (sigexp, f)

  fun parseSigExp' (LS.Cons ((L.ID (_, id), r), s)) =
      let
        let (sigexp, f') = parseWhereClauses' (LS.expose s, E.sigid (id, r))
      in
        (Parsing.Done (sigexp), f')
      end
    | parseSigExp' (f as LS.Cons ((L.LBRACE, r), _)) =
        (Parsing.Continuation (fn f' =>
         let
           let (sigexp, f'') = parseWhereClauses' (f', E.thesig)
         in
           (Parsing.Done (sigexp), f'')
         end), f)
    | parseSigExp' (LS.Cons ((t, r), _)) =
        Parsing.error (r, "Expected module type name or expression, found token "
                       ^ L.toString t)

  fun parseSgEqual' (idOpt, LS.Cons ((L.EQUAL, r), s')) =
        Parsing.recwith (parseSigExp', fun sigexp -> E.sigdef (idOpt, sigexp))
                        (LS.expose s')
    | parseSgEqual' (idOpt, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `=', found token " ^ L.toString t)

  fun parseSgDef' (LS.Cons ((L.ID (_, id), r), s')) =
        parseSgEqual' (SOME (id), LS.expose s')
    | parseSgDef' (LS.Cons ((L.UNDERSCORE, r), s')) =
        parseSgEqual' (NONE, LS.expose s')
    | parseSgDef' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected module type identifier, found token " ^ L.toString t)

  fun parseSigDef' (LS.Cons ((L.SIG, r), s')) =
        parseSgDef' (LS.expose s')

  fun parseStrDec2' (idOpt, LS.Cons ((L.COLON, r), s')) =
        Parsing.recwith (parseSigExp', fun sigexp -> E.structdec (idOpt, sigexp))
                        (LS.expose s')
    | parseStrDec2' (idOpt, LS.Cons ((L.EQUAL, r), s')) =
      let
        let (strexp, f') = parseStructExp' (LS.expose s')
      in
        (Parsing.Done (E.structdef (idOpt, strexp)), f')
      end
    | parseStrDec2' (idOpt, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t)

  fun parseStrDec' (LS.Cons ((L.ID (_, id), r), s')) =
        parseStrDec2' (SOME id, LS.expose s')
    | parseStrDec' (LS.Cons ((L.UNDERSCORE, r), s')) =
        parseStrDec2' (NONE, LS.expose s')
    | parseStrDec' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected module identifier, found token " ^ L.toString t)

  fun parseStructDec' (LS.Cons ((L.STRUCT, r), s')) =
        parseStrDec' (LS.expose s')

  fun parseInclude' (LS.Cons ((L.INCLUDE, r), s')) =
        parseSigExp' (LS.expose s')

  fun parseOpen' (LS.Cons ((L.OPEN, r), s')) =
        parseStructExp' (LS.expose s')

end
