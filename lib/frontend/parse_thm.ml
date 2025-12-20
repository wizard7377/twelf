(* Parsing Thm Declarations *)


(* Author: Carsten Schuermann *)


(* Modified: Brigitte Pientka *)


module ParseThm (ThmExtSyn' : THMEXTSYN) (ParseTerm : PARSE_TERM) : PARSE_THM = struct (*! structure Parsing = Parsing' !*)

module ThmExtSyn = ThmExtSyn'
module L = Lexer
module LS = LexerStream
module E = ThmExtSyn
module P = Paths
(*--------------------------*)

(* %terminates declarations *)

(*--------------------------*)

(* idToNat (region, (idCase, name)) = n
       where n an natural number indicated by name, which should consist
       of all digits.  Raises error otherwise, or if integer it too large
    *)

let rec idToNat (r, name)  = try L.stringToNat (name) with Overflow -> Parsing.error (r, "Integer too large") | L.NotDigit _ -> Parsing.error (r, "Identifier not a natural number")
let rec stripRParen = function (LS.Cons ((L.RPAREN, r), s')) -> LS.expose s' | (LS.Cons ((t, r), _)) -> Parsing.error (r, "Expected `)', found " ^ L.toString t)
let rec decideRBrace = function (r0, (orders, LS.Cons ((L.RBRACE, r), s'))) -> (Some (E.lex (r0, orders)), LS.expose s') | (r0, (order, LS.Cons ((t, r), _))) -> Parsing.error (P.join (r0, r), "Expected `}', found " ^ L.toString t)
let rec decideRBracket = function (r0, (orders, LS.Cons ((L.RBRACKET, r), s'))) -> (Some (E.simul (r0, orders)), LS.expose s') | (r0, (order, LS.Cons ((t, r), _))) -> Parsing.error (P.join (r0, r), "Expected `]', found " ^ L.toString t)
let rec decideRParen = function (r0, (ids, LS.Cons ((L.RPAREN, r), s'))) -> (Some (E.varg (r, ids)), LS.expose s') | (r0, (order, LS.Cons ((t, r), _))) -> Parsing.error (P.join (r0, r), "Expected `)', found " ^ L.toString t)
(* parseIds "id ... id" = ["id",...,"id"] *)

(* terminated by non-identifier token *)

let rec parseIds = function (LS.Cons ((L.ID (L.Upper, id), r), s')) -> ( let (ids, f') = parseIds (LS.expose s') in  (id :: ids, f') ) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expecter upper case identifier, found " ^ L.toString t) | f -> ([], f)
(* parseArgPat "_id ... _id" = [idOpt,...,idOpt] *)

(* terminated by token different from underscore or id *)

let rec parseArgPat = function (LS.Cons ((L.ID (L.Upper, id), r), s')) -> ( let (idOpts, f') = parseArgPat (LS.expose s') in  (Some id :: idOpts, f') ) | (LS.Cons ((L.ID (_, id), r), s')) -> Parsing.error (r, "Expected upper case identifier, found " ^ id) | (LS.Cons ((L.UNDERSCORE, r), s')) -> ( let (idOpts, f') = parseArgPat (LS.expose s') in  (None :: idOpts, f') ) | f -> ([], f)
(* parseCallPat "id _id ... _id" = (id, region, [idOpt,...,idOpt]) *)

let rec parseCallPat = function (LS.Cons ((L.ID (_, id), r), s')) -> ( let (idOpts, f') = parseArgPat (LS.expose s') in  ((id, idOpts, P.join (r, r')), f') ) | (LS.Cons ((t, r), s)) -> Parsing.error (r, "Expected call pattern, found token " ^ L.toString t)
(* parseCallPats "(id _id ... _id)...(id _id ... _id)." *)

let rec parseCallPats = function (LS.Cons ((L.LPAREN, r), s')) -> ( let (cpat, f') = parseCallPat (LS.expose s') in let (cpats, f'') = parseCallPats (stripRParen f') in  (cpat :: cpats, f'') ) | (f) -> ([], f) | (LS.Cons ((t, r), s)) -> Parsing.error (r, "Expected call patterns, found token " ^ L.toString t)
(* order ::= id | (id ... id)   virtual arguments = subterm ordering
               | {order ... order}  lexicgraphic order
               | [order ... order]  simultaneous order
    *)

(* parseOrderOpt (f) = (SOME(order), f') or (NONE, f) *)

(* returns an optional order and front of remaining stream *)

let rec parseOrderOpt = function (LS.Cons ((L.LPAREN, r), s')) -> decideRParen (r, parseIds (LS.expose s')) | (LS.Cons ((L.LBRACE, r), s')) -> decideRBrace (r, parseOrders (LS.expose s')) | (LS.Cons ((L.LBRACKET, r), s')) -> decideRBracket (r, parseOrders (LS.expose s')) | (LS.Cons ((L.ID (L.Upper, id), r), s')) -> (Some (E.varg (r, [id])), LS.expose s') | (f) -> (None, f)
and parseOrders (f)  = parseOrders' (parseOrderOpt f)
and parseOrders' = function (Some (order), f') -> ( let (orders, f'') = parseOrders f' in  (order :: orders, f'') ) | (None, f') -> ([], f')
(* parseOrder (f) = (order, f') *)

(* returns an order and front of remaining stream *)

let rec parseOrder (f)  = parseOrder' (parseOrderOpt f)
and parseOrder' = function (Some (order), f') -> (order, f') | (None, LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected order, found " ^ L.toString t)
(* parseTDecl "order callPats." *)

(* parses Termination Declaration, followed by `.' *)

let rec parseTDecl f  = ( let (order, f') = parseOrder f in let (callpats, f'') = parseCallPats f' in  (E.tdecl (order, E.callpats callpats), f'') )
(* parseTerminates' "%terminates tdecl." *)

let rec parseTerminates' (LS.Cons ((L.TERMINATES, r), s'))  = parseTDecl (LS.expose s')
(* ------------------- *)

(* %total declaration  *)

(* ------------------- *)

(* parseTotal' "%total tdecl." *)

let rec parseTotal' (LS.Cons ((L.TOTAL, r), s'))  = parseTDecl (LS.expose s')
(* ------------------- *)

(* %prove declarations *)

(* ------------------- *)

(* parsePDecl "id nat order callpats." *)

let rec parsePDecl = function (LS.Cons ((L.ID (_, id), r), s')) -> ( let depth = idToNat (r, id) in let (t', f') = parseTDecl (LS.expose s') in  (E.prove (depth, t'), f') ) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t)
(* parseProve' "%prove pdecl." *)

let rec parseProve' (LS.Cons ((L.PROVE, r), s'))  = parsePDecl (LS.expose s')
(* ----------------------- *)

(* %establish declarations *)

(* ----------------------- *)

(* parseEDecl "id nat order callpats." *)

let rec parseEDecl = function (LS.Cons ((L.ID (_, id), r), s')) -> ( let depth = idToNat (r, id) in let (t', f') = parseTDecl (LS.expose s') in  (E.establish (depth, t'), f') ) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t)
(* parseEstablish' "%establish pdecl." *)

let rec parseEstablish' (LS.Cons ((L.ESTABLISH, r), s'))  = parseEDecl (LS.expose s')
(* -------------------- *)

(* %assert declarations *)

(* -------------------- *)

(* parseAssert' "%assert cp" *)

let rec parseAssert' (LS.Cons ((L.ASSERT, r), s'))  = ( let (callpats, f'') = parseCallPats (LS.expose s') in  (E.assert (E.callpats callpats), f'') )
(* --------------------- *)

(* %theorem declarations *)

(* --------------------- *)

let rec stripRBrace = function (LS.Cons ((L.RBRACE, r), s')) -> (LS.expose s', r) | (LS.Cons ((t, r), _)) -> Parsing.error (r, "Expected `}', found " ^ L.toString t)
and parseDec (r, f)  = ( let ((x, yOpt), f') = ParseTerm.parseDec' f in let (f'', r2) = stripRBrace f' in let dec = (match yOpt with None -> E.ExtSyn.dec0 (x, P.join (r, r2)) | Some y -> E.ExtSyn.dec (x, y, P.join (r, r2))) in  (dec, f'') )
and parseDecs' = function (Drs, LS.Cons (BS)) -> ( let (Dr, f') = parseDec (r, LS.expose s') in  parseDecs' (E.decl (Drs, Dr), f') ) | Drs -> Drs
and parseDecs = function (LS.Cons (BS)) -> ( let (Dr, f') = parseDec (r, LS.expose s') in  parseDecs' (E.decl (E.null, Dr), f') ) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `{', found " ^ L.toString t)
let rec parsePi = function (LS.Cons ((L.ID (_, "pi"), r), s')) -> parseDecs (LS.expose s') | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `pi', found " ^ L.toString t)
let rec parseSome = function (gbs, LS.Cons ((L.ID (_, "some"), r), s')) -> ( let (g1, f') = parseDecs (LS.expose s') in let (g2, f'') = parsePi f' in  parseSome' ((g1, g2) :: gbs, f'') ) | (gbs, f) -> ( let (g2, f') = parsePi f in  parseSome' ((E.null, g2) :: gbs, f') ) | (gbs, f) -> (gbs, f) | (gbs, LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `some' or `pi', found " ^ L.toString t)
and parseSome' = function (gbs, f) -> (gbs, f) | (gbs, LS.Cons ((L.ID (_, "|"), r), s')) -> parseSome (gbs, LS.expose s') | (gbs, LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `)' or `|', found " ^ L.toString t)
let rec stripParen (gbs, LS.Cons ((L.RPAREN, r), s'))  = (gbs, LS.expose s')
let rec parseGBs = function (LS.Cons ((L.LPAREN, r), s')) -> stripParen (parseSome ([], LS.expose s')) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `(', found " ^ L.toString t)
let rec forallG ((gbs', f'), r)  = ( let (t'', f'') = parseForallStar f' in  (E.forallG (gbs', t''), f'') )
and forallStar ((g', f'), r)  = ( let (t'', f'') = parseForall f' in  (E.forallStar (g', t''), f'') )
and forall ((g', f'), r)  = ( let (t'', f'') = parseExists f' in  (E.forall (g', t''), f'') )
and exists ((g', f'), r)  = ( let (t'', f'') = parseTrue f' in  (E.exists (g', t''), f'') )
and top (f', r)  = (E.top, f')
and parseTrue = function (LS.Cons ((L.ID (_, "true"), r), s')) -> top (LS.expose s', r) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `true', found " ^ L.toString t)
and parseExists = function (LS.Cons ((L.ID (_, "exists"), r), s')) -> exists (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "true"), r), s')) -> top (LS.expose s', r) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `exists' or `true', found " ^ L.toString t)
and parseForall = function (LS.Cons ((L.ID (_, "forall"), r), s')) -> forall (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "exists"), r), s')) -> exists (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "true"), r), s')) -> top (LS.expose s', r) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `forall', `exists', or `true', found " ^ L.toString t)
and parseForallStar = function (LS.Cons ((L.ID (_, "forall*"), r), s')) -> forallStar (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "forall"), r), s')) -> forall (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "exists"), r), s')) -> exists (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "true"), r), s')) -> top (LS.expose s', r) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `forall*', `forall', `exists', or `true', found " ^ L.toString t)
and parseCtxScheme = function (LS.Cons ((L.ID (_, "forallG"), r), s')) -> forallG (parseGBs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "forall*"), r), s')) -> forallStar (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "forall"), r), s')) -> forall (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "exists"), r), s')) -> exists (parseDecs (LS.expose s'), r) | (LS.Cons ((L.ID (_, "true"), r), s')) -> top (LS.expose s', r) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `forallG', `forall*', `forall', `exists', or `true', found " ^ L.toString t)
(* parseColon ": mform" *)

let rec parseColon = function (LS.Cons ((L.COLON, r), s')) -> parseCtxScheme (LS.expose s') | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected `:', found " ^ L.toString t)
(* parseThDec "id : mform" *)

let rec parseThDec = function (LS.Cons ((L.ID (_, id), r), s')) -> ( let (t', f') = parseColon (LS.expose s') in  (E.dec (id, t'), f') ) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t)
(* parseTheoremDec' "%theorem thdec." *)

(* We enforce the quantifier alternation restriction syntactically *)

let rec parseTheoremDec' (LS.Cons ((L.THEOREM, r), s'))  = parseThDec (LS.expose s')
(*  -bp6/5/99. *)

(* parsePredicate f = (pred, f')               *)

(* parses the reduction predicate, <, <=, =   *)

let rec parsePredicate = function (LS.Cons ((L.ID (_, "<"), r), s')) -> (E.predicate ("LESS", r), (LS.expose s')) | (LS.Cons ((L.ID (_, "<="), r), s')) -> (E.predicate ("LEQ", r), (LS.expose s')) | (LS.Cons ((L.Eq, r), s')) -> (E.predicate ("EQUAL", r), (LS.expose s')) | (LS.Cons ((t, r), s')) -> Parsing.error (r, "Expected reduction predicate <, = or <=, found " ^ L.toString t)
(* parseRDecl "order callPats." *)

(* parses Reducer Declaration, followed by `.' *)

let rec parseRDecl f  = ( let (oOut, f1) = parseOrder f in let (p, f2) = parsePredicate f1 in let (oIn, f3) = parseOrder f2 in let (callpats, f4) = parseCallPats f3 in  (E.rdecl (p, oOut, oIn, E.callpats callpats), f4) )
(* parseReduces' "%reduces thedec. " *)

let rec parseReduces' (LS.Cons ((L.REDUCES, r), s'))  = parseRDecl (LS.expose s')
let rec parseTabledDecl (f)  = (match (LS.expose s') with (f) -> (E.tableddecl (id, r), f) | _ -> Parsing.error (r, "Expected ."))
(* parseTabled' "%tabled thedec. " *)

let rec parseTabled' (LS.Cons ((L.TABLED, r), s'))  = parseTabledDecl (LS.expose s')
let rec parseKeepTableDecl (f)  = (match (LS.expose s') with (f) -> (E.keepTabledecl (id, r), f) | _ -> Parsing.error (r, "Expected ."))
(* parseKeepTable' "%keepTabled thedec. " *)

let rec parseKeepTable' (LS.Cons ((L.KEEPTABLE, r), s'))  = parseKeepTableDecl (LS.expose s')
let rec parseWDecl f  = ( (*       val (GBs, f1) = parseGBs f *)
let (qids, f1) = ParseTerm.parseQualIds' f in let (callpats, f2) = parseCallPats f1 in  (E.wdecl (qids, E.callpats callpats), f2) )
let rec parseWorlds' (LS.Cons ((L.WORLDS, r), s'))  = parseWDecl (LS.expose s')
let parseTotal' = parseTotal'
let parseTerminates' = parseTerminates'
let parseTheorem' = parseForallStar
let parseTheoremDec' = parseTheoremDec'
let parseProve' = parseProve'
let parseEstablish' = parseEstablish'
let parseAssert' = parseAssert'
let parseReduces' = parseReduces'
(*  -bp  6/05/99.*)

let parseTabled' = parseTabled'
(*  -bp 20/11/01.*)

let parseKeepTable' = parseKeepTable'
(*  -bp 20/11/01.*)

let parseWorlds' = parseWorlds'
(* local ... in *)

 end


(* functor Parser *)

