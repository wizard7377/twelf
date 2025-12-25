open Basis
(* Parsing Terms and Declarations *)

(* Author: Frank Pfenning *)

module type PARSE_TERM = sig
  (*! structure Parsing : Parsing.PARSING !*)
  module ExtSyn : Recon_term.EXTSYN

  val parseQualId' : string list * Parsing.lexResult Parsing.parser
  val parseQualIds' : string list * string list Parsing.parser
  val parseFreeze' : string list * string list Parsing.parser

  val parseSubord' :
    (string list * string) * (string list * string) list Parsing.parser

  val parseThaw' : string list * string list Parsing.parser
  val parseDeterministic' : string list * string list Parsing.parser
  val parseCompile' : string list * string list Parsing.parser

  (* -ABP 4/4/03 *)
  val parseTerm' : ExtSyn.term Parsing.parser
  val parseDec' : string option * ExtSyn.term option Parsing.parser
  val parseCtx' : ExtSyn.dec list Parsing.parser
end

(* signature Parse_prg.PARSE_TERM *)
(* Parsing Terms and Variable Declarations *)

(* Author: Frank Pfenning *)

module ParseTerm (ExtSyn' : Recon_term.EXTSYN) (Names : Names.NAMES) :
  Parse_prg.PARSE_TERM = struct
  (*! structure Parsing = Parsing' !*)

  module ExtSyn = ExtSyn'
  (* some shorthands *)

  module L = Lexer
  module LS = LexerStream
  (*! structure Paths = Lexer.Paths !*)

  module FX = NamesFixity
  (* Operators and atoms for_sml operator precedence parsing *)

  type 'a operator =
    | Atom of 'a
    | Infix of (FX.precedence * FX.associativity) * ('a * 'a -> 'a)
    | Prefix of FX.precedence * ('a -> 'a)
    | Postfix of FX.precedence * ('a -> 'a)
  (* Predeclared infix operators *)

  let juxOp = Infix ((FX.inc FX.maxPrec, FX.Left), ExtSyn.app)
  (* juxtaposition *)

  let arrowOp = Infix ((FX.dec FX.minPrec, FX.Right), ExtSyn.arrow)
  let backArrowOp = Infix ((FX.dec FX.minPrec, FX.Left), ExtSyn.backarrow)
  let colonOp = Infix ((FX.dec (FX.dec FX.minPrec), FX.Left), ExtSyn.hastype)

  let rec infixOp (infixity, tm) =
    Infix (infixity, fun (tm1, tm2) -> ExtSyn.app (ExtSyn.app (tm, tm1), tm2))

  let rec prefixOp (prec, tm) = Prefix (prec, fun tm1 -> ExtSyn.app (tm, tm1))
  let rec postfixOp (prec, tm) = Postfix (prec, fun tm1 -> ExtSyn.app (tm, tm1))

  let rec idToTerm = function
    | L.Lower, ids, name, r -> ExtSyn.lcid (ids, name, r)
    | L.Upper, ids, name, r -> ExtSyn.ucid (ids, name, r)
    | L.Quoted, ids, name, r -> ExtSyn.quid (ids, name, r)

  let rec isQuoted = function L.Quoted -> true | _ -> false

  type stack = ExtSyn.term operator list
  type opr = ExtSyn.term operator
  (* The next section deals generically with fixity parsing          *)

  (* Because of juxtaposition, it is not clear how to turn this      *)

  (* into a separate module without passing a juxtaposition operator *)

  (* into the shift and resolve functions                            *)

  module P : sig
    val reduce : stack -> stack
    val reduceAll : Paths.region * stack -> ExtSyn.term
    val shiftAtom : ExtSyn.term * stack -> stack
    val shift : Paths.region * opr * stack -> stack
    val resolve : Paths.region * opr * stack -> stack
  end = struct
    (* Stack invariants, refinements of operator list *)

    (*
         <p>       ::= <pStable> | <pRed>
         <pStable> ::= <pAtom> | <pOp?>
         <pAtom>   ::= Atom _ :: <pOp?>
         <pOp?>    ::= nil | <pOp>
         <pOp>     ::= Infix _ :: <pAtom> :: <pOp?>
                     | Prefix _ :: <pOp?>
         <pRed>    ::= Postfix _ :: Atom _ :: <pOp?>
                     | Atom _ :: <pOp>
      *)

    (* val reduce : <pRed> -> <p> *)

    let rec reduce = function
      | Atom tm2 :: Infix (_, con) :: Atom tm1 :: p' ->
          Atom (con (tm1, tm2)) :: p'
      | Atom tm :: Prefix (_, con) :: p' -> Atom (con tm) :: p'
      | Postfix (_, con) :: Atom tm :: p' -> Atom (con tm) :: p'
    (* no other cases should be possible by stack invariant *)

    (* val reduceRec : <pStable> -> ExtSyn.term *)

    let rec reduceRec = function Atom e :: [] -> e | p -> reduceRec (reduce p)
    (* val reduceAll : <p> -> ExtSyn.term *)

    let rec reduceAll = function
      | r, Atom e :: [] -> e
      | r, Infix _ :: p' -> Parsing.error (r, "Incomplete infix expression")
      | r, Prefix _ :: p' -> Parsing.error (r, "Incomplete prefix expression")
      | r, [] -> Parsing.error (r, "Empty expression")
      | r, p -> reduceRec (reduce p)
    (* val shiftAtom : term * <pStable> -> <p> *)

    (* does not raise Error exception *)

    let rec shiftAtom = function
      | tm, p -> reduce (Atom tm :: juxOp :: p)
      | tm, p -> Atom tm :: p
    (* val shift : Paths.region * opr * <pStable> -> <p> *)

    let rec shift = function
      | r, opr, p -> reduce (opr :: juxOp :: p)
      | r, Infix _, Infix _ :: p' ->
          Parsing.error (r, "Consective infix operators")
      | r, Infix _, Prefix _ :: p' ->
          Parsing.error (r, "Infix operator following prefix operator")
      | r, Infix _, [] -> Parsing.error (r, "Leading infix operator")
      | r, opr, p -> opr :: juxOp :: p
      | r, Postfix _, Infix _ :: p' ->
          Parsing.error (r, "Postfix operator following infix operator")
      | r, Postfix _, Prefix _ :: p' ->
          Parsing.error (r, "Postfix operator following prefix operator")
      | r, Postfix _, [] -> Parsing.error (r, "Leading postfix operator")
      | r, opr, p -> opr :: p
    (* val resolve : Paths.region * opr * <pStable> -> <p> *)

    (* Decides, based on precedence of opr compared to the top of the
         stack whether to shift the new operator or reduce the stack
      *)

    let rec resolve = function
      | r, opr, p -> (
          match (FX.compare (prec, prec'), assoc, assoc') with
          | Gt, _, _ -> shift (r, opr, p)
          | Lt, _, _ -> resolve (r, opr, reduce p)
          | Eq, FX.Left, FX.Left -> resolve (r, opr, reduce p)
          | Eq, FX.Right, FX.Right -> shift (r, opr, p)
          | _ ->
              Parsing.error
                (r, "Ambiguous: infix following infix of identical precedence"))
      | r, opr, p -> (
          match FX.compare (prec, prec') with
          | Gt -> shift (r, opr, p)
          | Lt -> resolve (r, opr, reduce p)
          | Eq ->
              Parsing.error
                (r, "Ambiguous: infix following prefix of identical precedence")
          )
      | r, opr, p -> shift (r, opr, p)
      | r, opr, p -> (
          match FX.compare (prec, prec') with
          | Gt -> reduce (shift (r, opr, p))
          | Lt -> resolve (r, opr, reduce p)
          | Eq ->
              Parsing.error
                ( r,
                  "Ambiguous: postfix following prefix of identical precedence"
                ))
      | r, opr, p -> (
          match FX.compare (prec, prec') with
          | Gt -> reduce (shift (r, opr, p))
          | Lt -> resolve (r, opr, reduce p)
          | Eq ->
              Parsing.error
                (r, "Ambiguous: postfix following infix of identical precedence")
          )
      | r, opr, p -> reduce (shift (r, opr, p))
      | r, opr, p -> shift (r, opr, p)
  end
  (* structure P *)

  (* parseQualifier' f = (ids, f')
       pre: f begins with L.ID

       Note: precondition for_sml recursive call is enforced by the lexer. *)

  let rec parseQualId' f =
    match LS.expose s' with
    | LS.Cons ((L.Paths.PATHSEP, _), s'') ->
        let (ids, (t, r)), f' = parseQualId' (LS.expose s'') in
        ((id :: ids, (t, r)), f')
    | f' -> (([], (t, r)), f')

  let rec stripBar = function
    | LS.Cons ((L.ID (_, "|"), r), s') -> LS.expose s'
    | f -> f
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected `|', found token " ^ L.toString t)

  let rec parseQualIds1 = function
    | ls, f ->
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        let r = Paths.join (r0, r1) in
        let f'' = stripBar f' in
        parseQualIds1 ((ids, name) :: ls, f'')
    | ls, LS.Cons ((L.RPAREN, r), s') -> (ls, LS.expose s')
    | ls, LS.Cons ((t, r), s) ->
        Parsing.error (r, "Expected label, found token " ^ L.toString t)

  let rec parseQualIds' = function
    | LS.Cons ((L.LPAREN, r), s') -> parseQualIds1 ([], LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected list of labels, found token " ^ L.toString t)
  (* Copied from parse-mode, should probably try to abstract all
       of the strip* functions into a common location - gaw *)

  let rec stripRParen = function
    | LS.Cons ((L.RPAREN, r), s') -> LS.expose s'
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected closing `)', found " ^ L.toString t)

  let rec parseSubordPair2 = function
    | f, qid ->
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        ((qid, (ids, name)), stripRParen f')
    | LS.Cons ((t, r), s'), qid ->
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  let rec parseSubordPair1 = function
    | f ->
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        parseSubordPair2 (f', (ids, name))
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  let rec parseSubord' = function
    | LS.Cons ((L.LPAREN, r), s'), qidpairs ->
        let qidpair, f = parseSubordPair1 (LS.expose s') in
        parseSubord' (f, qidpair :: qidpairs)
    | f, qidpairs -> (List.rev qidpairs, f)
    | LS.Cons ((t, r), s'), qidpairs ->
        Parsing.error
          (r, "Expected a pair of identifiers, found token " ^ L.toString t)

  let rec parseFreeze' = function
    | f, qids ->
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        parseFreeze' (f', (ids, name) :: qids)
    | f, qids -> (List.rev qids, f)
    | LS.Cons ((t, r), s'), qids ->
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  let rec parseThaw' (f, qids) =
    (* same %freeze *)
    parseFreeze' (f, qids)

  let rec parseDeterministic' = function
    | f, qids ->
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        parseDeterministic' (f', (ids, name) :: qids)
    | f, qids -> (List.rev qids, f)
    | LS.Cons ((t, r), s'), qids ->
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)
  (* ABP 4/4/03 *)

  let rec parseCompile' = function
    | f, qids ->
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        parseCompile' (f', (ids, name) :: qids)
    | f, qids -> (List.rev qids, f)
    | LS.Cons ((t, r), s'), qids ->
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)
  (* val parseExp : (L.token * L.region) LS.stream * <p>
                        -> ExtSyn.term * (L.token * L.region) LS.front *)

  let rec parseExp (s, p) = parseExp' (LS.expose s, p)

  and parseExp' = function
    | f, p -> (
        let (ids, (L.ID (idCase, name), r1)), f' = parseQualId' f in
        let r = Paths.join (r0, r1) in
        let tm = idToTerm (idCase, ids, name, r) in
        (* Currently, we cannot override fixity status of identifiers *)
        (* Thus isQuoted always returns false *)
        if isQuoted idCase then parseExp' (f', P.shiftAtom (tm, p))
        else
          match Names.fixityLookup (Names.Qid (ids, name)) with
          | FX.Nonfix -> parseExp' (f', P.shiftAtom (tm, p))
          | FX.Infix infixity ->
              parseExp' (f', P.resolve (r, infixOp (infixity, tm), p))
          | FX.Prefix prec ->
              parseExp' (f', P.resolve (r, prefixOp (prec, tm), p))
          | FX.Postfix prec ->
              parseExp' (f', P.resolve (r, postfixOp (prec, tm), p)))
    | LS.Cons ((L.UNDERSCORE, r), s), p ->
        parseExp (s, P.shiftAtom (ExtSyn.omitted r, p))
    | LS.Cons ((L.TYPE, r), s), p -> parseExp (s, P.shiftAtom (ExtSyn.typ r, p))
    | LS.Cons ((L.COLON, r), s), p -> parseExp (s, P.resolve (r, colonOp, p))
    | LS.Cons ((L.BACKARROW, r), s), p ->
        parseExp (s, P.resolve (r, backArrowOp, p))
    | LS.Cons ((L.ARROW, r), s), p -> parseExp (s, P.resolve (r, arrowOp, p))
    | LS.Cons ((L.LPAREN, r), s), p -> decideRParen (r, parseExp (s, []), p)
    | f, p -> (P.reduceAll (r, p), f)
    | LS.Cons ((L.LBRACE, r), s), p -> decideRBrace (r, parseDec s, p)
    | f, p -> (P.reduceAll (r, p), f)
    | LS.Cons ((L.LBRACKET, r), s), p -> decideRBracket (r, parseDec s, p)
    | f, p -> (P.reduceAll (r, p), f)
    | f, p -> (P.reduceAll (r, p), f)
    | f, p -> (P.reduceAll (r, p), f)
    | f, p -> (P.reduceAll (r, p), f)
    | f, p -> (P.reduceAll (r, p), f)
    | f, p -> (P.reduceAll (r, p), f)
    | LS.Cons ((L.STRING str, r), s), p ->
        parseExp (s, P.shiftAtom (ExtSyn.scon (str, r), p))
    | LS.Cons ((t, r), s), p ->
        Parsing.error
          (r, "Unexpected token " ^ L.toString t ^ " found in expression")

  and parseDec s = parseDec' (LS.expose s)

  and parseDec' = function
    | LS.Cons ((L.ID (L.Quoted, name), r), s') ->
        Parsing.error (r, "Illegal bound quoted identifier " ^ name)
    | LS.Cons ((L.ID (idCase, name), r), s') -> (
        match Names.fixityLookup (Names.Qid ([], name)) with
        | FX.Nonfix -> parseDec1 (Some name, LS.expose s')
        | FX.Infix _ -> Parsing.error (r, "Cannot bind infix identifier " ^ name)
        | FX.Prefix _ ->
            Parsing.error (r, "Cannot bind prefix identifier " ^ name)
        | FX.Postfix _ ->
            Parsing.error (r, "Cannot bind postfix identifier " ^ name))
    | LS.Cons ((L.UNDERSCORE, r), s') -> parseDec1 (None, LS.expose s')
    | LS.Cons ((L.EOF, r), s') ->
        Parsing.error (r, "Unexpected end of stream in declaration")
    | LS.Cons ((t, r), s') ->
        Parsing.error (r, "Expected variable name, found token " ^ L.toString t)

  and parseDec1 = function
    | x, LS.Cons ((L.COLON, r), s') ->
        let tm, f'' = parseExp (s', []) in
        ((x, Some tm), f'')
    | x, f -> ((x, None), f)
    | x, f -> ((x, None), f)
    | x, LS.Cons ((t, r), s') ->
        Parsing.error
          (r, "Expected optional type declaration, found token " ^ L.toString t)

  and decideRParen = function
    | r0, (tm, LS.Cons ((L.RPAREN, r), s)), p ->
        parseExp (s, P.shiftAtom (tm, p))
    | r0, (tm, LS.Cons ((_, r), s)), p ->
        Parsing.error (Paths.join (r0, r), "Unmatched open parenthesis")

  and decideRBrace = function
    | r0, ((x, yOpt), LS.Cons ((L.RBRACE, r), s)), p ->
        let dec =
          match yOpt with
          | None -> ExtSyn.dec0 (x, Paths.join (r0, r))
          | Some y -> ExtSyn.dec (x, y, Paths.join (r0, r))
        in
        let tm, f' = parseExp (s, []) in
        parseExp' (f', P.shiftAtom (ExtSyn.pi (dec, tm), p))
    | r0, (_, LS.Cons ((_, r), s)), p ->
        Parsing.error (Paths.join (r0, r), "Unmatched open brace")

  and decideRBracket = function
    | r0, ((x, yOpt), LS.Cons ((L.RBRACKET, r), s)), p ->
        let dec =
          match yOpt with
          | None -> ExtSyn.dec0 (x, Paths.join (r0, r))
          | Some y -> ExtSyn.dec (x, y, Paths.join (r0, r))
        in
        let tm, f' = parseExp (s, []) in
        parseExp' (f', P.shiftAtom (ExtSyn.lam (dec, tm), p))
    | r0, (dec, LS.Cons ((_, r), s)), p ->
        Parsing.error (Paths.join (r0, r), "Unmatched open bracket")
  (* Parses contexts of the form  G ::= {id:term} | G, {id:term} *)

  let rec stripRBrace = function
    | LS.Cons ((L.RBRACE, r), s') -> (LS.expose s', r)
    | LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected `}', found " ^ L.toString t)

  and parseBracedDec (r, f) =
    let (x, yOpt), f' = parseDec' f in
    let f'', r2 = stripRBrace f' in
    let d =
      match yOpt with
      | None -> ExtSyn.dec0 (x, Paths.join (r, r2))
      | Some y -> ExtSyn.dec (x, y, Paths.join (r, r2))
    in
    (d, f'')
  (* parseCtx (b, ds, f) = ds'
       if   f is a stream "{x1:V1}...{xn:Vn} s"
       and  b is true if no declarations has been parsed yet
       and  ds is a context of declarations
       then ds' = ds, x1:V1, ..., xn:Vn
    *)

  let rec parseCtx = function
    | b, ds, LS.Cons BS ->
        let d, f' = parseBracedDec (r, LS.expose s') in
        parseCtx (false, d :: ds, f')
    | b, ds, f ->
        if b then Parsing.error (r, "Expected `{', found " ^ L.toString t)
        else (ds, f)

  let parseQualId' = parseQualId'
  let parseQualIds' = parseQualIds'
  let parseSubord' = fun f -> parseSubord' (f, [])
  let parseFreeze' = fun f -> parseFreeze' (f, [])
  let parseThaw' = fun f -> parseThaw' (f, [])
  let parseDeterministic' = fun f -> parseDeterministic' (f, [])
  let parseCompile' = fun f -> parseCompile' (f, [])
  (* -ABP 4/4/03 *)

  let parseTerm' = fun f -> parseExp' (f, [])
  let parseDec' = parseDec'
  let parseCtx' = fun f -> parseCtx (true, [], f)
  (* local ... in *)
end

(* functor ParseTerm *)
