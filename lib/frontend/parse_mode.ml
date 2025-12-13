(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) ParseMode
   ((*! structure Paths : PATHS !*)
   (*! structure Parsing' : PARSING !*)
   (*! sharing Parsing'.Lexer.Paths = Paths !*)
   structure ExtModes' : EXTMODES
   (*! sharing ExtModes'.Paths = Paths !*)
   (*! sharing ExtModes'.ExtSyn.Paths = Paths !*)
   structure ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ExtModes'.ExtSyn)
     : PARSE_MODE =
struct
  (*! structure Parsing = Parsing' !*)
  structure ExtModes = ExtModes'

  local
    structure L = Lexer
    structure LS = Lexer.Stream
    structure E = ExtModes
    structure P = Paths

    (* extract (s, i) = substring of s starting at index i
       Effect: raises Subscript if i > |s|
    *)
    fun extract (s, i) =
        if i = String.size s
          then NONE
        else SOME (String.extract (s, i, NONE))

    (* splitModeId (r, id) = (mode, idOpt) where id = "<mode><idOpt>"
       Invariant: id <> ""
    *)
    fun splitModeId (r, id) =
        case String.sub (id, 0)
          of #"*" => (E.star r, extract (id, 1))
           | #"-" => (if (String.size id > 1 andalso String.sub (id, 1) = #"1")
                        then (E.minus1 r, extract (id, 2))
                      else (E.minus r, extract (id, 1)))
           | #"+" => (E.plus r,  extract (id, 1))
           | _ => Parsing.error (r, "Expected mode `+', `-', `*', or `-1'  found " ^ id)

    fun (* GEN BEGIN FUN FIRST *) validateMArg (r, mId as (mode, SOME (id))) =
        if L.isUpper id
          then mId
        else Parsing.error (r, "Expected free uppercase variable, found " ^ id) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) validateMArg (r, (_, NONE)) =
          Parsing.error (r, "Missing variable following mode") (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) validateMode (r, (mode, NONE)) = mode (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) validateMode (r, (_, SOME(id))) =
           Parsing.error (r, "Expected simple mode, found mode followed by identifier " ^ id) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) stripRParen (LS.Cons ((L.RPAREN, r), s')) = (LS.expose s', r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripRParen (LS.Cons ((t, r), s')) = (* t = `.' or ? *)
          Parsing.error (r, "Expected closing `)', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) stripRBrace (LS.Cons ((L.RBRACE, r), s')) = (LS.expose s', r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripRBrace (LS.Cons ((t, r), _))  =
          Parsing.error (r, "Expected `}', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseShortSpine "modeid ... modeid." *)
    fun (* GEN BEGIN FUN FIRST *) parseShortSpine (f as LS.Cons ((L.DOT, r), s')) =
          (E.Short.mnil r, f) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseShortSpine (f as LS.Cons ((L.RPAREN, r), s')) =
          (E.Short.mnil r, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseShortSpine (LS.Cons ((L.ID (_, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val mId = validateMArg (r, splitModeId (r, id)) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (mS', f') = parseShortSpine (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (E.Short.mapp (mId, mS'), f')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseShortSpine (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected mode or `.', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseFull "mode {id:term} ... mode {x:term} term" *)
    fun (* GEN BEGIN FUN FIRST *) parseFull (LS.Cons (t0 as (L.ID (c, id), r0), s'), r1) =
        (* Look ahead one token to decide if quantifier follows *)
        (case LS.expose s'
           of LS.Cons ((L.LBRACE, r), s'') =>
              (* found quantifier --- id must be mode *)
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val mId = splitModeId (r0, id) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val m = validateMode (r0, mId) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val ((x, yOpt), f') = ParseTerm.parseDec' (LS.expose s'') (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (f'', r') = stripRBrace f' (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val dec = (case yOpt
                             of NONE => ParseTerm.ExtSyn.dec0 (x, P.join (r, r'))
                              | SOME y => ParseTerm.ExtSyn.dec (x, y, P.join (r, r'))) (* GEN END TAG OUTSIDE LET *)
                (* GEN BEGIN TAG OUTSIDE LET *) val (t', f''') = parseFull (f'', r1) (* GEN END TAG OUTSIDE LET *)
              in
                (E.Full.mpi (m, dec, t'), f''')
              end
            | LS.Cons TS =>
              (* no quantifier --- parse atomic type *)
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val (t', f' as LS.Cons ((_, r), s')) =
                    ParseTerm.parseTerm' (LS.Cons (t0, LS.cons TS)) (* GEN END TAG OUTSIDE LET *)
              in
                (E.Full.mroot (t', P.join (r, r1)), f')
              end) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseFull (LS.Cons ((L.LPAREN, r0), s'), r1) =
        (* Left paren --- parse atomic type *)
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t', f') = ParseTerm.parseTerm' (LS.expose s') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (f'', r') = stripRParen f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.Full.mroot (t', P.join (r', r1)), f'')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseFull (LS.Cons ((t, r), s'), _) =
          Parsing.error (r, "Expected mode or identifier, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseMode2 switches between full and short mode declarations *)
    (* lexid could be mode or other identifier *)
    fun (* GEN BEGIN FUN FIRST *) parseMode2 (lexid, LS.Cons (BS as ((L.LBRACE, r), s')), r1) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t', f') = parseFull (LS.Cons (lexid, LS.cons BS), r1) (* GEN END TAG OUTSIDE LET *)
        in
          (E.Full.toModedec t', f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseMode2 ((L.ID (_, name), r), f, _) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (mS', f') = parseShortSpine f (* GEN END TAG OUTSIDE LET *)
        in
          (E.Short.toModedec (E.Short.mroot (nil, name, r, mS')), f')
        end (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parseModeParen (LS.Cons ((L.ID (_, name), r0), s'), r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (mS', f') = parseShortSpine (LS.expose s') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (f'', r') = stripRParen f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.Short.toModedec (E.Short.mroot (nil, name, P.join (r, r'), mS')), f'')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseModeParen (LS.Cons ((t, r), s'), _) =
          Parsing.error (r, "Expected identifier, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseMode1 parses mdecl *)
    fun (* GEN BEGIN FUN FIRST *) parseMode1 (LS.Cons (lexid as (L.ID _, r), s')) =
          parseModeNext (parseMode2 (lexid, LS.expose s', r)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseMode1 (LS.Cons ((L.LPAREN, r), s')) =
          parseModeNext (parseModeParen (LS.expose s', r)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseMode1 (LS.Cons ((t, r), _)) =
          Parsing.error (r, "Expected identifier or mode, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) parseModeNext (modedec, f as LS.Cons ((L.DOT, _), s')) = (modedec::nil, f) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseModeNext (modedec, f) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (mdecs, f') = parseMode1 f (* GEN END TAG OUTSIDE LET *)
        in
          (modedec::mdecs, f')
        end (* GEN END FUN BRANCH *)

    (* parseMode' : lexResult front -> modedec * lexResult front
       Invariant: exposed input stream starts with MODE
    *)
    fun (* GEN BEGIN FUN FIRST *) parseMode' (LS.Cons ((L.MODE, r), s')) = parseMode1 (LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseMode' (LS.Cons ((L.UNIQUE, r), s')) = parseMode1 (LS.expose s') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseMode' (LS.Cons ((L.COVERS, r), s')) = parseMode1 (LS.expose s') (* GEN END FUN BRANCH *)
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val parseMode' = parseMode' (* GEN END TAG OUTSIDE LET *)
  end  (* local *)

end (* GEN END FUNCTOR DECL *);  (* functor ParseMode *)
