(* Parsing Thm Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor (* GEN BEGIN FUNCTOR DECL *) ParseThm
  ((*! structure Paths : PATHS *)
   (*! structure Parsing' : PARSING !*)
   (*! sharing Parsing'.Lexer.Paths = Paths !*)
   structure ThmExtSyn' : THMEXTSYN
   (*! sharing ThmExtSyn'.Paths = Paths !*)
   (*! sharing ThmExtSyn'.ExtSyn.Paths = Paths !*)
   structure ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ThmExtSyn'.ExtSyn)
     : PARSE_THM =
struct
  (*! structure Parsing = Parsing' !*)
  structure ThmExtSyn = ThmExtSyn'

  local
    structure L = Lexer
    structure LS = Lexer.Stream
    structure E = ThmExtSyn
    structure P = Paths

    (*--------------------------*)
    (* %terminates declarations *)
    (*--------------------------*)

    (* idToNat (region, (idCase, name)) = n
       where n an natural number indicated by name, which should consist
       of all digits.  Raises error otherwise, or if integer it too large
    *)
    fun idToNat (r, name) =
      L.stringToNat (name)
      handle Overflow => Parsing.error (r, "Integer too large")
           | L.NotDigit _ => Parsing.error (r, "Identifier not a natural number")

    fun (* GEN BEGIN FUN FIRST *) stripRParen (LS.Cons ((L.RPAREN, r), s')) = LS.expose s' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripRParen (LS.Cons ((t, r), _))  =
          Parsing.error (r, "Expected `)', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) decideRBrace (r0, (orders, LS.Cons ((L.RBRACE, r), s'))) =
          (SOME(E.lex (r0, orders)), LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decideRBrace (r0, (order, LS.Cons ((t, r), _)))  =
          Parsing.error (P.join(r0,r), "Expected `}', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) decideRBracket (r0, (orders, LS.Cons ((L.RBRACKET, r), s'))) =
          (SOME(E.simul (r0, orders)), LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decideRBracket (r0, (order, LS.Cons ((t, r), _)))  =
          Parsing.error (P.join(r0,r), "Expected `]', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) decideRParen (r0, (ids, LS.Cons ((L.RPAREN, r), s'))) =
          (SOME(E.varg (r,ids)), LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decideRParen (r0, (order, LS.Cons ((t, r), _)))  =
          Parsing.error (P.join(r0,r), "Expected `)', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseIds "id ... id" = ["id",...,"id"] *)
    (* terminated by non-identifier token *)
    fun (* GEN BEGIN FUN FIRST *) parseIds (LS.Cons ((L.ID (L.Upper, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (ids, f') = parseIds (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (id :: ids, f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseIds (LS.Cons ((t as L.ID (_, id), r), s')) =
        Parsing.error (r, "Expecter upper case identifier, found " ^ L.toString t) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseIds f = (nil, f) (* GEN END FUN BRANCH *)

    (* parseArgPat "_id ... _id" = [idOpt,...,idOpt] *)
    (* terminated by token different from underscore or id *)
    fun (* GEN BEGIN FUN FIRST *) parseArgPat (LS.Cons ((L.ID (L.Upper, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (idOpts, f') = parseArgPat (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (SOME id :: idOpts, f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseArgPat (LS.Cons ((L.ID (_, id), r), s')) =
        Parsing.error (r, "Expected upper case identifier, found " ^ id) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseArgPat (LS.Cons ((L.UNDERSCORE, r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (idOpts, f') = parseArgPat (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (NONE :: idOpts, f')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseArgPat f = (nil, f) (* GEN END FUN BRANCH *)

    (* parseCallPat "id _id ... _id" = (id, region, [idOpt,...,idOpt]) *)
    fun (* GEN BEGIN FUN FIRST *) parseCallPat (LS.Cons ((L.ID (_, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (idOpts, f' as LS.Cons ((_ ,r'), _)) = parseArgPat (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          ((id, idOpts, P.join (r, r')), f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseCallPat (LS.Cons ((t, r), s)) =
        Parsing.error (r, "Expected call pattern, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseCallPats "(id _id ... _id)...(id _id ... _id)." *)
    fun (* GEN BEGIN FUN FIRST *) parseCallPats (LS.Cons ((L.LPAREN, r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (cpat, f') = parseCallPat (LS.expose s') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (cpats, f'') = parseCallPats (stripRParen f') (* GEN END TAG OUTSIDE LET *)
        in
          (cpat::cpats, f'')
        end (* GEN END FUN FIRST *)
      (* Parens around call patterns no longer optional *)
      | (* GEN BEGIN FUN BRANCH *) parseCallPats (f as LS.Cons ((L.DOT, r), s')) =
          (nil, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseCallPats (LS.Cons ((t, r), s)) =
        Parsing.error (r, "Expected call patterns, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* order ::= id | (id ... id)   virtual arguments = subterm ordering
               | {order ... order}  lexicgraphic order
               | [order ... order]  simultaneous order
    *)
    (* parseOrderOpt (f) = (SOME(order), f') or (NONE, f) *)
    (* returns an optional order and front of remaining stream *)
    fun (* GEN BEGIN FUN FIRST *) parseOrderOpt (LS.Cons ((L.LPAREN, r), s')) =
          decideRParen (r, parseIds (LS.expose s')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseOrderOpt (LS.Cons ((L.LBRACE, r), s')) =
          decideRBrace (r, parseOrders (LS.expose s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseOrderOpt (LS.Cons ((L.LBRACKET, r), s')) =
          decideRBracket (r, parseOrders (LS.expose s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseOrderOpt (LS.Cons ((L.ID (L.Upper, id), r), s')) =
          (SOME (E.varg (r, [id])), LS.expose s') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseOrderOpt (f as LS.Cons (_, s')) = (NONE, f) (* GEN END FUN BRANCH *)

    (* parseOrders (f) = ([order1,...,ordern], f') *)
    (* returns a sequence of orders and remaining front of stream *)
    and parseOrders (f) = parseOrders' (parseOrderOpt f)
    and (* GEN BEGIN FUN FIRST *) parseOrders' (SOME(order), f') =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (orders, f'') = parseOrders f' (* GEN END TAG OUTSIDE LET *)
        in
          (order::orders, f'')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseOrders' (NONE, f') = (nil, f') (* GEN END FUN BRANCH *)

    (* parseOrder (f) = (order, f') *)
    (* returns an order and front of remaining stream *)
    fun parseOrder (f) = parseOrder' (parseOrderOpt f)
    and (* GEN BEGIN FUN FIRST *) parseOrder' (SOME(order), f') = (order, f') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseOrder' (NONE, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected order, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseTDecl "order callPats." *)
    (* parses Termination Declaration, followed by `.' *)
    fun parseTDecl f =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (order, f') = parseOrder f (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (callpats, f'') = parseCallPats f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.tdecl (order, E.callpats callpats), f'')
        end

    (* parseTerminates' "%terminates tdecl." *)
    fun parseTerminates' (LS.Cons ((L.TERMINATES, r), s')) =
          parseTDecl (LS.expose s')

    (* ------------------- *)
    (* %total declaration  *)
    (* ------------------- *)

    (* parseTotal' "%total tdecl." *)
    fun parseTotal' (LS.Cons ((L.TOTAL, r), s')) =
          parseTDecl (LS.expose s')

    (* ------------------- *)
    (* %prove declarations *)
    (* ------------------- *)

    (* parsePDecl "id nat order callpats." *)
    fun (* GEN BEGIN FUN FIRST *) parsePDecl (LS.Cons ((L.ID (_, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val depth = idToNat (r, id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (t', f') = parseTDecl (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (E.prove (depth, t'), f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parsePDecl (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseProve' "%prove pdecl." *)
    fun parseProve' (LS.Cons ((L.PROVE, r), s')) =
          parsePDecl (LS.expose s')


    (* ----------------------- *)
    (* %establish declarations *)
    (* ----------------------- *)

    (* parseEDecl "id nat order callpats." *)
    fun (* GEN BEGIN FUN FIRST *) parseEDecl (LS.Cons ((L.ID (_, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val depth = idToNat (r, id) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (t', f') = parseTDecl (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (E.establish (depth, t'), f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseEDecl (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseEstablish' "%establish pdecl." *)
    fun parseEstablish' (LS.Cons ((L.ESTABLISH, r), s')) =
          parseEDecl (LS.expose s')

    (* -------------------- *)
    (* %assert declarations *)
    (* -------------------- *)

    (* parseAssert' "%assert cp" *)
    fun parseAssert' (LS.Cons ((L.ASSERT, r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (callpats, f'') = parseCallPats (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (E.assert (E.callpats callpats), f'')
        end

    (* --------------------- *)
    (* %theorem declarations *)
    (* --------------------- *)

    fun (* GEN BEGIN FUN FIRST *) stripRBrace (LS.Cons ((L.RBRACE, r), s')) = (LS.expose s', r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripRBrace (LS.Cons ((t, r), _))  =
          Parsing.error (r, "Expected `}', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseDec "{id:term} | {id}" *)
    and parseDec (r, f) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((x, yOpt), f') = ParseTerm.parseDec' f (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (f'', r2) = stripRBrace f' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val dec = (case yOpt
                       of NONE => E.ExtSyn.dec0 (x, P.join (r, r2))
                        | SOME y => E.ExtSyn.dec (x, y, P.join (r, r2))) (* GEN END TAG OUTSIDE LET *)
        in
          (dec, f'')
        end

    (* parseDecs' "{id:term}...{id:term}", zero or more, ":term" optional *)
    and (* GEN BEGIN FUN FIRST *) parseDecs' (Drs, LS.Cons (BS as ((L.LBRACE, r), s'))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Dr, f') = parseDec (r, LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          parseDecs' (E.decl (Drs, Dr), f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseDecs' Drs = Drs (* GEN END FUN BRANCH *)

    (* parseDecs "{id:term}...{id:term}", one ore more, ":term" optional *)
    and (* GEN BEGIN FUN FIRST *) parseDecs (LS.Cons (BS as ((L.LBRACE, r), s'))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (Dr, f') = parseDec (r, LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          parseDecs' (E.decl (E.null, Dr), f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseDecs (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `{', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parsePi (LS.Cons ((L.ID (_, "pi"), r), s')) =
          parseDecs (LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parsePi (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `pi', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parseSome (gbs, LS.Cons ((L.ID (_, "some"), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (g1, f') = parseDecs (LS.expose s') (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (g2, f'') = parsePi f' (* GEN END TAG OUTSIDE LET *)
        in
          parseSome' ((g1,g2)::gbs, f'')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseSome (gbs, f as LS.Cons ((L.ID (_, "pi"), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (g2, f') = parsePi f (* GEN END TAG OUTSIDE LET *)
        in
          parseSome' ((E.null, g2)::gbs, f')
        end (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseSome (gbs, f as LS.Cons ((L.RPAREN, r), s')) = (gbs, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseSome (gbs, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `some' or `pi', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) parseSome' (gbs, f as LS.Cons ((L.RPAREN, r), s')) = (gbs, f) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseSome' (gbs, LS.Cons ((L.ID (_, "|"), r), s')) =
          parseSome (gbs, LS.expose s') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseSome' (gbs, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `)' or `|', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun stripParen (gbs, LS.Cons ((L.RPAREN, r), s')) = (gbs, LS.expose s')

    fun (* GEN BEGIN FUN FIRST *) parseGBs (LS.Cons ((L.LPAREN, r), s')) =
          stripParen (parseSome (nil, LS.expose s')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseGBs (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `(', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun forallG ((gbs', f'), r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t'', f'') = parseForallStar f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.forallG (gbs', t''), f'')
        end

    and forallStar ((g', f'), r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t'', f'') = parseForall f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.forallStar (g', t''),  f'')
        end

    and forall ((g', f'), r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t'', f'') = parseExists f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.forall (g', t''), f'')
        end

    and exists ((g', f'), r) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t'', f'') = parseTrue f' (* GEN END TAG OUTSIDE LET *)
        in
          (E.exists (g', t''), f'')
        end

    and top (f', r) = (E.top, f')

    (* parseTrue "true" *)
    and (* GEN BEGIN FUN FIRST *) parseTrue (LS.Cons ((L.ID (_, "true"), r), s')) =
          top (LS.expose s', r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseTrue (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `true', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseExists "exists decs mform | mform" *)
    and (* GEN BEGIN FUN FIRST *) parseExists (LS.Cons ((L.ID (_, "exists"), r), s')) =
          exists (parseDecs (LS.expose s'), r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseExists (LS.Cons ((L.ID (_, "true"), r), s')) =
          top (LS.expose s', r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExists (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `exists' or `true', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseForall "forall decs mform | mform" *)
    and (* GEN BEGIN FUN FIRST *) parseForall (LS.Cons ((L.ID (_, "forall"), r), s')) =
          forall (parseDecs (LS.expose s'), r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseForall (LS.Cons ((L.ID (_, "exists"), r), s')) =
          exists (parseDecs (LS.expose s'), r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseForall (LS.Cons ((L.ID (_, "true"), r), s')) =
          top (LS.expose s', r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseForall (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `forall', `exists', or `true', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseForallStar "forall* decs mform | mform" *)
    and (* GEN BEGIN FUN FIRST *) parseForallStar (LS.Cons ((L.ID (_, "forall*"), r), s')) =
          forallStar (parseDecs (LS.expose s'), r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseForallStar (LS.Cons ((L.ID (_, "forall"), r), s')) =
          forall (parseDecs (LS.expose s'), r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseForallStar (LS.Cons ((L.ID (_, "exists"), r), s')) =
          exists (parseDecs (LS.expose s'), r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseForallStar (LS.Cons ((L.ID (_, "true"), r), s')) =
          top (LS.expose s', r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseForallStar (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `forall*', `forall', `exists', or `true', found "
                             ^ L.toString t) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) parseCtxScheme (LS.Cons ((L.ID (_, "forallG"), r), s')) =
           forallG (parseGBs (LS.expose s'), r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseCtxScheme (LS.Cons ((L.ID (_, "forall*"), r), s')) =
           forallStar (parseDecs (LS.expose s'), r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseCtxScheme (LS.Cons ((L.ID (_, "forall"), r), s')) =
          forall (parseDecs (LS.expose s'), r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseCtxScheme (LS.Cons ((L.ID (_, "exists"), r), s')) =
          exists (parseDecs (LS.expose s'), r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseCtxScheme (LS.Cons ((L.ID (_, "true"), r), s')) =
          top (LS.expose s', r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseCtxScheme (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `forallG', `forall*', `forall', `exists', or `true', found "
                             ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseColon ": mform" *)
    fun (* GEN BEGIN FUN FIRST *) parseColon (LS.Cons ((L.COLON, r), s')) =
          parseCtxScheme (LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseColon (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `:', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseThDec "id : mform" *)
    fun (* GEN BEGIN FUN FIRST *) parseThDec (LS.Cons ((L.ID (_, id), r), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (t', f') = parseColon (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          (E.dec (id, t'), f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseThDec (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseTheoremDec' "%theorem thdec." *)
    (* We enforce the quantifier alternation restriction syntactically *)
    fun parseTheoremDec' (LS.Cons ((L.THEOREM, r), s')) =
          parseThDec (LS.expose s')

    (*  -bp6/5/99. *)

    (* parsePredicate f = (pred, f')               *)
    (* parses the reduction predicate, <, <=, =   *)
    fun (* GEN BEGIN FUN FIRST *) parsePredicate (LS.Cons ((L.ID(_, "<"), r), s')) = (E.predicate ("LESS", r), (LS.expose s')) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parsePredicate (LS.Cons ((L.ID(_, "<="), r), s')) = (E.predicate ("LEQ", r), (LS.expose s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parsePredicate (LS.Cons ((L.EQUAL, r), s')) = (E.predicate ("EQUAL", r), (LS.expose s')) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parsePredicate (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected reduction predicate <, = or <=, found " ^ L.toString t) (* GEN END FUN BRANCH *)


    (* parseRDecl "order callPats." *)
    (* parses Reducer Declaration, followed by `.' *)
    fun parseRDecl f =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (oOut, f1) = parseOrder f (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (p, f2) = parsePredicate f1 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (oIn, f3) = parseOrder f2 (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (callpats, f4) = parseCallPats f3 (* GEN END TAG OUTSIDE LET *)
        in
            (E.rdecl (p, oOut, oIn, E.callpats callpats), f4)
        end

   (* parseReduces' "%reduces thedec. " *)
   fun parseReduces' (LS.Cons ((L.REDUCES, r), s')) =
        parseRDecl (LS.expose s')


    fun parseTabledDecl (f as LS.Cons ((L.ID (_, id), r), s'))=
          (case (LS.expose s') of
             (f as LS.Cons ((L.DOT, r'), s)) =>  (E.tableddecl (id, r), f)
            | _ => Parsing.error (r, "Expected ."))


  (* parseTabled' "%tabled thedec. " *)
   fun parseTabled' (LS.Cons ((L.TABLED, r), s')) =
        parseTabledDecl (LS.expose s')


   fun parseKeepTableDecl (f as LS.Cons ((L.ID (_, id), r), s'))=
          (case (LS.expose s') of
             (f as LS.Cons ((L.DOT, r'), s)) =>  (E.keepTabledecl (id, r), f)
            | _ => Parsing.error (r, "Expected ."))


  (* parseKeepTable' "%keepTabled thedec. " *)
   fun parseKeepTable' (LS.Cons ((L.KEEPTABLE, r), s')) =
        parseKeepTableDecl (LS.expose s')


   fun parseWDecl f =
       let
   (*       val (GBs, f1) = parseGBs f *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (qids, f1) = ParseTerm.parseQualIds' f (* GEN END TAG OUTSIDE LET *)
         (* GEN BEGIN TAG OUTSIDE LET *) val (callpats,f2) = parseCallPats f1 (* GEN END TAG OUTSIDE LET *)
       in
         (E.wdecl (qids, E.callpats callpats), f2)
       end

   fun parseWorlds' (LS.Cons ((L.WORLDS, r), s')) =
        parseWDecl (LS.expose s')


  in
    (* GEN BEGIN TAG OUTSIDE LET *) val parseTotal' = parseTotal' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseTerminates' = parseTerminates' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseTheorem' = parseForallStar (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseTheoremDec' = parseTheoremDec' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseProve' = parseProve' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseEstablish' = parseEstablish' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseAssert' = parseAssert' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseReduces' = parseReduces' (* GEN END TAG OUTSIDE LET *)           (*  -bp  6/05/99.*)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseTabled' = parseTabled' (* GEN END TAG OUTSIDE LET *)             (*  -bp 20/11/01.*)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseKeepTable' = parseKeepTable' (* GEN END TAG OUTSIDE LET *)               (*  -bp 20/11/01.*)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseWorlds' = parseWorlds' (* GEN END TAG OUTSIDE LET *)
  end  (* local ... in *)

end (* GEN END FUNCTOR DECL *);  (* functor Parser *)



