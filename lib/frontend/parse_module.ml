(* Parsing modules *)
(* Author: Kevin Watkins *)

functor (* GEN BEGIN FUNCTOR DECL *) ParseModule
  ((*! structure Paths : PATHS !*)
   (*! structure Parsing' : PARSING !*)
   (*! sharing Parsing'.Lexer.Paths = Paths !*)
   structure ModExtSyn' : MODEXTSYN
   (*! sharing ModExtSyn'.Paths = Paths !*)
   structure ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ModExtSyn'.ExtSyn)
  : PARSE_MODULE =
struct

  (*! structure Parsing = Parsing' !*)
  structure ModExtSyn = ModExtSyn'

  structure L = Lexer
  structure LS = Lexer.Stream
  structure E = ModExtSyn

  fun (* GEN BEGIN FUN FIRST *) parseStructExp' (f as LS.Cons ((L.ID _, r0), _)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (_, id), r1)), f') = ParseTerm.parseQualId' f (* GEN END TAG OUTSIDE LET *)
      in
        (E.strexp (ids, id, Paths.join (r0, r1)), f')
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseStructExp' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseColonEqual' (LS.Cons ((L.COLON, r1), s')) =
      (case LS.expose s'
         of LS.Cons ((L.EQUAL, _), s'') => ((), LS.expose s'')
          | LS.Cons ((t, r2), s'') =>
              Parsing.error (r2, "Expected `=', found token " ^ L.toString t)) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseColonEqual' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `:=', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseDot' (LS.Cons ((L.DOT, r), s')) = (r, LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseDot' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `.', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseConInst' (f as LS.Cons ((L.ID _, r0), _)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (_, id), r1)), f1) = ParseTerm.parseQualId' (f) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (_, f2) = parseColonEqual' (f1) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (tm, f3) = ParseTerm.parseTerm' (f2) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (r2, f4) = parseDot' (f3) (* GEN END TAG OUTSIDE LET *)
      in
        (E.coninst ((ids, id, Paths.join (r0, r1)), tm, Paths.join (r0, r2)),
         f4)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseConInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseStrInst2' (r0, f as LS.Cons ((L.ID _, r1), _)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (_, id), r2)), f1) = ParseTerm.parseQualId' (f) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (_, f2) = parseColonEqual' (f1) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (strexp, f3) = parseStructExp' (f2) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (r3, f4) = parseDot' (f3) (* GEN END TAG OUTSIDE LET *)
      in
        (E.strinst ((ids, id, Paths.join (r1, r2)),
                    strexp, Paths.join (r0, r3)),
         f4)
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseStrInst2' (r0, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseStrInst' (LS.Cons ((L.STRUCT, r), s')) =
        parseStrInst2' (r, LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseStrInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `%struct', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseInsts' (f as LS.Cons ((L.ID _, _), _)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (inst, f') = parseConInst' (f) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (insts, f'') = parseInsts' (f') (* GEN END TAG OUTSIDE LET *)
      in
        (inst::insts, f'')
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseInsts' (f as LS.Cons ((L.STRUCT, _), _)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (inst, f') = parseStrInst' (f) (* GEN END TAG OUTSIDE LET *)
        (* GEN BEGIN TAG OUTSIDE LET *) val (insts, f'') = parseInsts' (f') (* GEN END TAG OUTSIDE LET *)
      in
        (inst::insts, f'')
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) parseInsts' (LS.Cons ((L.RBRACE, _), s')) =
        (nil, LS.expose s') (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) parseInsts' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier or `%struct', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseInstantiate' (f as LS.Cons ((L.LBRACE, _), s')) =
        parseInsts' (LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseInstantiate' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `{', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseWhereClauses' (f as LS.Cons ((L.WHERE, _), s'), sigexp) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (insts, f') = parseInstantiate' (LS.expose s') (* GEN END TAG OUTSIDE LET *)
      in
        parseWhereClauses' (f', E.wheresig (sigexp, insts))
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseWhereClauses' (f, sigexp) = (sigexp, f) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseSigExp' (LS.Cons ((L.ID (_, id), r), s)) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (sigexp, f') = parseWhereClauses' (LS.expose s, E.sigid (id, r)) (* GEN END TAG OUTSIDE LET *)
      in
        (Parsing.Done (sigexp), f')
      end (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseSigExp' (f as LS.Cons ((L.LBRACE, r), _)) =
        (Parsing.Continuation ((* GEN BEGIN FUNCTION EXPRESSION *) fn f' =>
         let
           (* GEN BEGIN TAG OUTSIDE LET *) val (sigexp, f'') = parseWhereClauses' (f', E.thesig) (* GEN END TAG OUTSIDE LET *)
         in
           (Parsing.Done (sigexp), f'')
         end (* GEN END FUNCTION EXPRESSION *)), f) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) parseSigExp' (LS.Cons ((t, r), _)) =
        Parsing.error (r, "Expected signature name or expression, found token "
                       ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseSgEqual' (idOpt, LS.Cons ((L.EQUAL, r), s')) =
        Parsing.recwith (parseSigExp', (* GEN BEGIN FUNCTION EXPRESSION *) fn sigexp => E.sigdef (idOpt, sigexp) (* GEN END FUNCTION EXPRESSION *))
                        (LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseSgEqual' (idOpt, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `=', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseSgDef' (LS.Cons ((L.ID (_, id), r), s')) =
        parseSgEqual' (SOME (id), LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseSgDef' (LS.Cons ((L.UNDERSCORE, r), s')) =
        parseSgEqual' (NONE, LS.expose s') (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) parseSgDef' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected signature identifier, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun parseSigDef' (LS.Cons ((L.SIG, r), s')) =
        parseSgDef' (LS.expose s')

  fun (* GEN BEGIN FUN FIRST *) parseStrDec2' (idOpt, LS.Cons ((L.COLON, r), s')) =
        Parsing.recwith (parseSigExp', (* GEN BEGIN FUNCTION EXPRESSION *) fn sigexp => E.structdec (idOpt, sigexp) (* GEN END FUNCTION EXPRESSION *))
                        (LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseStrDec2' (idOpt, LS.Cons ((L.EQUAL, r), s')) =
      let
        (* GEN BEGIN TAG OUTSIDE LET *) val (strexp, f') = parseStructExp' (LS.expose s') (* GEN END TAG OUTSIDE LET *)
      in
        (Parsing.Done (E.structdef (idOpt, strexp)), f')
      end (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) parseStrDec2' (idOpt, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun (* GEN BEGIN FUN FIRST *) parseStrDec' (LS.Cons ((L.ID (_, id), r), s')) =
        parseStrDec2' (SOME id, LS.expose s') (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) parseStrDec' (LS.Cons ((L.UNDERSCORE, r), s')) =
        parseStrDec2' (NONE, LS.expose s') (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) parseStrDec' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

  fun parseStructDec' (LS.Cons ((L.STRUCT, r), s')) =
        parseStrDec' (LS.expose s')

  fun parseInclude' (LS.Cons ((L.INCLUDE, r), s')) =
        parseSigExp' (LS.expose s')

  fun parseOpen' (LS.Cons ((L.OPEN, r), s')) =
        parseStructExp' (LS.expose s')

end (* GEN END FUNCTOR DECL *)
