(* Parsing Mode Declarations *)

(* Author: Carsten Schuermann *)

module type PARSE_MODE = sig
  (*! structure Parsing : Parsing.PARSING !*)
  module ExtModes : Recon_mode.EXTMODES

  val parseMode' : ExtModes.modedec list Parsing.parser
end

(* signature Parse_prg.PARSE_MODE *)
(* Parsing Mode Declarations *)

(* Author: Carsten Schuermann *)

module ParseMode (ExtModes' : Recon_mode.EXTMODES) (ParseTerm : Parse_prg.Parse_term.PARSE_TERM) : Parse_prg.PARSE_MODE =
struct
  (*! structure Parsing = Parsing' !*)

  module ExtModes = ExtModes'
  module L = Lexer
  module LS = LexerStream
  module E = ExtModes
  module P = Paths
  (* extract (s, i) = substring of s starting at index i
       Effect: raises Subscript if i > |s|
    *)

  let rec extract (s, i) =
    if i = String.size s then None else Some (String.extract (s, i, None))
  (* splitModeId (r, id) = (mode, idOpt) where id = "<mode><idOpt>"
       Invariant: id <> ""
    *)

  let rec splitModeId (r, id) =
    match String.sub (id, 0) with
    | '*' -> (E.star r, extract (id, 1))
    | '-' ->
        if String.size id > 1 && String.sub (id, 1) = '1' then
          (E.minus1 r, extract (id, 2))
        else (E.minus r, extract (id, 1))
    | '+' -> (E.plus r, extract (id, 1))
    | _ -> Parsing.error (r, "Expected mode `+', `-', `*', or `-1'  found " ^ id)

  let rec validateMArg = function
    | r, mId ->
        if L.isUpper id then mId
        else Parsing.error (r, "Expected free uppercase variable, found " ^ id)
    | r, (_, None) -> Parsing.error (r, "Missing variable following mode")

  let rec validateMode = function
    | r, (mode, None) -> mode
    | r, (_, Some id) ->
        Parsing.error
          (r, "Expected simple mode, found mode followed by identifier " ^ id)

  let rec stripRParen = function
    | LS.Cons ((L.RPAREN, r), s') -> (LS.expose s', r)
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected closing `)', found " ^ L.toString t)

  let rec stripRBrace = function
    | LS.Cons ((L.RBRACE, r), s') -> (LS.expose s', r)
    | LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected `}', found " ^ L.toString t)
  (* parseShortSpine "modeid ... modeid." *)

  let rec parseShortSpine = function
    | f -> (E.Short.mnil r, f)
    | f -> (E.Short.mnil r, f)
    | LS.Cons ((L.ID (_, id), r), s') ->
        let mId = validateMArg (r, splitModeId (r, id)) in
        let mS', f' = parseShortSpine (LS.expose s') in
        (E.Short.mapp (mId, mS'), f')
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected mode or `.', found " ^ L.toString t)
  (* parseFull "mode {id:term} ... mode {x:term} term" *)

  let rec parseFull = function
    | LS.Cons (t0, s'), r1 -> (
        match LS.expose s' with
        | LS.Cons ((L.LBRACE, r), s'') ->
            (* found quantifier --- id must be mode *)
            let mId = splitModeId (r0, id) in
            let m = validateMode (r0, mId) in
            let (x, yOpt), f' = ParseTerm.parseDec' (LS.expose s'') in
            let f'', r' = stripRBrace f' in
            let dec =
              match yOpt with
              | None -> ParseTerm.ExtSyn.dec0 (x, P.join (r, r'))
              | Some y -> ParseTerm.ExtSyn.dec (x, y, P.join (r, r'))
            in
            let t', f''' = parseFull (f'', r1) in
            (E.Full.mpi (m, dec, t'), f''')
        | LS.Cons TS ->
            (* no quantifier --- parse atomic type *)
            let t', f' = ParseTerm.parseTerm' (LS.Cons (t0, LS.cons TS)) in
            (E.Full.mroot (t', P.join (r, r1)), f'))
    | LS.Cons ((L.LPAREN, r0), s'), r1 ->
        let t', f' = ParseTerm.parseTerm' (LS.expose s') in
        let f'', r' = stripRParen f' in
        (E.Full.mroot (t', P.join (r', r1)), f'')
    | LS.Cons ((t, r), s'), _ ->
        Parsing.error (r, "Expected mode or identifier, found " ^ L.toString t)
  (* parseMode2 switches between full and short mode declarations *)

  (* lexid could be mode or other identifier *)

  let rec parseMode2 = function
    | lexid, LS.Cons BS, r1 ->
        let t', f' = parseFull (LS.Cons (lexid, LS.cons BS), r1) in
        (E.Full.toModedec t', f')
    | (L.ID (_, name), r), f, _ ->
        let mS', f' = parseShortSpine f in
        (E.Short.toModedec (E.Short.mroot ([], name, r, mS')), f')

  let rec parseModeParen = function
    | LS.Cons ((L.ID (_, name), r0), s'), r ->
        let mS', f' = parseShortSpine (LS.expose s') in
        let f'', r' = stripRParen f' in
        (E.Short.toModedec (E.Short.mroot ([], name, P.join (r, r'), mS')), f'')
    | LS.Cons ((t, r), s'), _ ->
        Parsing.error (r, "Expected identifier, found " ^ L.toString t)
  (* parseMode1 parses mdecl *)

  let rec parseMode1 = function
    | LS.Cons (lexid, s') -> parseModeNext (parseMode2 (lexid, LS.expose s', r))
    | LS.Cons ((L.LPAREN, r), s') ->
        parseModeNext (parseModeParen (LS.expose s', r))
    | LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected identifier or mode, found " ^ L.toString t)

  and parseModeNext = function
    | modedec, f -> (modedec :: [], f)
    | modedec, f ->
        let mdecs, f' = parseMode1 f in
        (modedec :: mdecs, f')
  (* parseMode' : lexResult front -> modedec * lexResult front
       Invariant: exposed input stream starts with MODE
    *)

  let rec parseMode' = function
    | LS.Cons ((L.MODE, r), s') -> parseMode1 (LS.expose s')
    | LS.Cons ((L.Unique.UNIQUE, r), s') -> parseMode1 (LS.expose s')
    | LS.Cons ((L.Cover.COVERS, r), s') -> parseMode1 (LS.expose s')

  let parseMode' = parseMode'
  (* local *)
end

(* functor ParseMode *)
