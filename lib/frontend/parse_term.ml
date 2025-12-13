(* Parsing Terms and Variable Declarations *)
(* Author: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) ParseTerm
  ((*! structure Parsing' : PARSING !*)
   structure ExtSyn' : EXTSYN
   (*! sharing Parsing'.Lexer.Paths = ExtSyn'.Paths !*)
   structure Names : NAMES)
  : PARSE_TERM =
struct

  (*! structure Parsing = Parsing' !*)
  structure ExtSyn = ExtSyn'

  local
    (* some shorthands *)
    structure L = Lexer
    structure LS = Lexer.Stream
    (*! structure Paths = Lexer.Paths !*)
    structure FX = Names.Fixity

    (* Operators and atoms for operator precedence parsing *)
    datatype 'a operator =
        Atom of 'a
      | Infix of (FX.precedence * FX.associativity) * ('a * 'a -> 'a)
      | Prefix of FX.precedence * ('a -> 'a)
      | Postfix of FX.precedence * ('a -> 'a)

    (* Predeclared infix operators *)
    (* GEN BEGIN TAG OUTSIDE LET *) val juxOp = Infix ((FX.inc FX.maxPrec, FX.Left), ExtSyn.app) (* GEN END TAG OUTSIDE LET *) (* juxtaposition *)
    (* GEN BEGIN TAG OUTSIDE LET *) val arrowOp = Infix ((FX.dec FX.minPrec, FX.Right), ExtSyn.arrow) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val backArrowOp = Infix ((FX.dec FX.minPrec, FX.Left), ExtSyn.backarrow) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val colonOp = Infix ((FX.dec (FX.dec FX.minPrec), FX.Left), ExtSyn.hastype) (* GEN END TAG OUTSIDE LET *)

    fun infixOp (infixity, tm) =
          Infix (infixity, ((* GEN BEGIN FUNCTION EXPRESSION *) fn (tm1, tm2) => ExtSyn.app (ExtSyn.app (tm, tm1), tm2) (* GEN END FUNCTION EXPRESSION *)))
    fun prefixOp (prec, tm) =
          Prefix (prec, ((* GEN BEGIN FUNCTION EXPRESSION *) fn tm1 => ExtSyn.app (tm, tm1) (* GEN END FUNCTION EXPRESSION *)))
    fun postfixOp (prec, tm) =
          Postfix (prec, ((* GEN BEGIN FUNCTION EXPRESSION *) fn tm1 => ExtSyn.app (tm, tm1) (* GEN END FUNCTION EXPRESSION *)))

    fun (* GEN BEGIN FUN FIRST *) idToTerm (L.Lower, ids, name, r) = ExtSyn.lcid (ids, name, r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) idToTerm (L.Upper, ids, name, r) = ExtSyn.ucid (ids, name, r) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) idToTerm (L.Quoted, ids, name, r) = ExtSyn.quid (ids, name, r) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) isQuoted (L.Quoted) = true (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) isQuoted _ = false (* GEN END FUN BRANCH *)

    type stack = (ExtSyn.term operator) list
    type opr = ExtSyn.term operator

    (* The next section deals generically with fixity parsing          *)
    (* Because of juxtaposition, it is not clear how to turn this      *)
    (* into a separate module without passing a juxtaposition operator *)
    (* into the shift and resolve functions                            *)

    structure P :>
      sig
        val reduce : stack -> stack
        val reduceAll : Paths.region * stack -> ExtSyn.term
        val shiftAtom : ExtSyn.term * stack -> stack
        val shift : Paths.region * opr * stack -> stack
        val resolve : Paths.region * opr * stack -> stack
      end =
    struct
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
      fun (* GEN BEGIN FUN FIRST *) reduce (Atom(tm2)::Infix(_,con)::Atom(tm1)::p') =
             Atom(con(tm1,tm2))::p' (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) reduce (Atom(tm)::Prefix(_,con)::p') = Atom(con(tm))::p' (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) reduce (Postfix(_,con)::Atom(tm)::p') = Atom(con(tm))::p' (* GEN END FUN BRANCH *)
        (* no other cases should be possible by stack invariant *)

      (* val reduceRec : <pStable> -> ExtSyn.term *)
      fun (* GEN BEGIN FUN FIRST *) reduceRec (Atom(e)::nil) = e (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) reduceRec (p) = reduceRec (reduce p) (* GEN END FUN BRANCH *)

      (* val reduceAll : <p> -> ExtSyn.term *)
      fun (* GEN BEGIN FUN FIRST *) reduceAll (r, Atom(e)::nil) = e (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) reduceAll (r, Infix _::p') = Parsing.error (r, "Incomplete infix expression") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) reduceAll (r, Prefix _::p') = Parsing.error (r, "Incomplete prefix expression") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) reduceAll (r, nil) = Parsing.error (r, "Empty expression") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) reduceAll (r, p) = reduceRec (reduce p) (* GEN END FUN BRANCH *)

      (* val shiftAtom : term * <pStable> -> <p> *)
      (* does not raise Error exception *)
      fun (* GEN BEGIN FUN FIRST *) shiftAtom (tm, p as (Atom _::p')) =
          (* insert juxOp operator and reduce *)
          (* juxtaposition binds most strongly *)
            reduce (Atom(tm)::juxOp::p) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) shiftAtom (tm, p) = Atom(tm)::p (* GEN END FUN BRANCH *)

      (* val shift : Paths.region * opr * <pStable> -> <p> *)
      fun (* GEN BEGIN FUN FIRST *) shift (r, opr as Atom _, p as (Atom _::p')) =
            (* insert juxOp operator and reduce *)
            (* juxtaposition binds most strongly *)
            reduce (opr::juxOp::p) (* GEN END FUN FIRST *)
        (* Atom/Infix: shift *)
        (* Atom/Prefix: shift *)
        (* Atom/Postfix cannot arise *)
        (* Atom/Empty: shift *)
        (* Infix/Atom: shift *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, Infix _, Infix _::p') =
            Parsing.error (r, "Consective infix operators") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, Infix _, Prefix _::p') =
            Parsing.error (r, "Infix operator following prefix operator") (* GEN END FUN BRANCH *)
        (* Infix/Postfix cannot arise *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, Infix _, nil) =
            Parsing.error (r, "Leading infix operator") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, opr as Prefix _, p as (Atom _::p')) =
           (* insert juxtaposition operator *)
           (* will be reduced later *)
           opr::juxOp::p (* GEN END FUN BRANCH *)
        (* Prefix/{Infix,Prefix,Empty}: shift *)
        (* Prefix/Postfix cannot arise *)
        (* Postfix/Atom: shift, reduced immediately *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, Postfix _, Infix _::p') =
            Parsing.error (r, "Postfix operator following infix operator") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, Postfix _, Prefix _::p') =
            Parsing.error (r, "Postfix operator following prefix operator") (* GEN END FUN BRANCH *)
        (* Postfix/Postfix cannot arise *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, Postfix _, nil) =
            Parsing.error (r, "Leading postfix operator") (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) shift (r, opr, p) = opr::p (* GEN END FUN BRANCH *)

      (* val resolve : Paths.region * opr * <pStable> -> <p> *)
      (* Decides, based on precedence of opr compared to the top of the
         stack whether to shift the new operator or reduce the stack
      *)
      fun (* GEN BEGIN FUN FIRST *) resolve (r, opr as Infix((prec, assoc), _),
                     p as (Atom(_)::Infix((prec', assoc'), _)::p')) =
          (case (FX.compare(prec,prec'), assoc, assoc')
             of (GREATER,_,_) => shift(r, opr, p)
              | (LESS,_,_) => resolve (r, opr, reduce(p))
              | (EQUAL, FX.Left, FX.Left) => resolve (r, opr, reduce(p))
              | (EQUAL, FX.Right, FX.Right) => shift(r, opr, p)
              | _ => Parsing.error (r, "Ambiguous: infix following infix of identical precedence")) (* GEN END FUN FIRST *)
        | (* GEN BEGIN FUN BRANCH *) resolve (r, opr as Infix ((prec, assoc), _),
                     p as (Atom(_)::Prefix(prec', _)::p')) =
          (case FX.compare(prec,prec')
             of GREATER => shift(r, opr, p)
              | LESS => resolve (r, opr, reduce(p))
              | EQUAL => Parsing.error (r, "Ambiguous: infix following prefix of identical precedence")) (* GEN END FUN BRANCH *)
        (* infix/atom/atom cannot arise *)
        (* infix/atom/postfix cannot arise *)
        (* infix/atom/<empty>: shift *)

        (* always shift prefix *)
        | (* GEN BEGIN FUN BRANCH *) resolve (r, opr as Prefix _, p) =
            shift(r, opr, p) (* GEN END FUN BRANCH *)

        (* always reduce postfix, possibly after prior reduction *)
        | (* GEN BEGIN FUN BRANCH *) resolve (r, opr as Postfix(prec, _),
                     p as (Atom _::Prefix(prec', _)::p')) =
            (case FX.compare(prec,prec')
               of GREATER => reduce (shift (r, opr, p))
                | LESS => resolve (r, opr, reduce (p))
                | EQUAL => Parsing.error (r, "Ambiguous: postfix following prefix of identical precedence")) (* GEN END FUN BRANCH *)
        (* always reduce postfix *)
        | (* GEN BEGIN FUN BRANCH *) resolve (r, opr as Postfix(prec, _),
                     p as (Atom _::Infix((prec', _), _)::p')) =
            (case FX.compare(prec,prec')
               of GREATER => reduce (shift (r, opr, p))
                | LESS => resolve (r, opr, reduce (p))
                | EQUAL => Parsing.error (r, "Ambiguous: postfix following infix of identical precedence")) (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) resolve (r, opr as Postfix _, p as (Atom _::nil)) =
            reduce (shift (r, opr, p)) (* GEN END FUN BRANCH *)

        (* default is shift *)
        | (* GEN BEGIN FUN BRANCH *) resolve (r, opr, p) =
            shift(r, opr, p) (* GEN END FUN BRANCH *)

    end  (* structure P *)

    (* parseQualifier' f = (ids, f')
       pre: f begins with L.ID

       Note: precondition for recursive call is enforced by the lexer. *)
    fun parseQualId' (f as LS.Cons ((t as L.ID (_, id), r), s')) =
        (case LS.expose s'
           of LS.Cons ((L.PATHSEP, _), s'') =>
              let
                (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (t, r)), f') = parseQualId' (LS.expose s'') (* GEN END TAG OUTSIDE LET *)
              in
                ((id::ids, (t, r)), f')
              end
            | f' => ((nil, (t, r)), f'))


    fun (* GEN BEGIN FUN FIRST *) stripBar (LS.Cons ((L.ID (_, "|"), r), s')) = (LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripBar (f as LS.Cons ((L.RPAREN, r), s')) = f (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) stripBar (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected `|', found token " ^ L.toString t) (* GEN END FUN BRANCH *)



    fun (* GEN BEGIN FUN FIRST *) parseQualIds1 (ls, f as LS.Cons ((t as L.ID (_, id), r0), s')) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r = Paths.join (r0, r1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val f'' = stripBar f' (* GEN END TAG OUTSIDE LET *)
        in
          parseQualIds1 ((ids, name) :: ls, f'')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseQualIds1 (ls,  LS.Cons ((L.RPAREN, r), s')) =
         (ls, LS.expose s') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseQualIds1 (ls, LS.Cons ((t, r), s)) =
         Parsing.error (r, "Expected label, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parseQualIds' (LS.Cons ((L.LPAREN, r), s')) =
        parseQualIds1 (nil, LS.expose s') (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseQualIds' (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected list of labels, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* Copied from parse-mode, should probably try to abstract all
       of the strip* functions into a common location - gaw *)
    fun (* GEN BEGIN FUN FIRST *) stripRParen (LS.Cons ((L.RPAREN, r), s')) = LS.expose s' (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripRParen (LS.Cons ((t, r), s')) = (* t = `.' or ? *)
          Parsing.error (r, "Expected closing `)', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parseSubordPair2 (f as LS.Cons ((L.ID _, _), _), qid) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
        in
          ((qid, (ids, name)), stripRParen f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseSubordPair2 (LS.Cons ((t, r), s'), qid) =
          Parsing.error (r, "Expected identifier, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parseSubordPair1 (f as LS.Cons ((L.ID _, _), _)) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
        in
          parseSubordPair2(f', (ids, name))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseSubordPair1 (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected identifier, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)

    fun (* GEN BEGIN FUN FIRST *) parseSubord' (LS.Cons ((L.LPAREN, r), s'), qidpairs) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (qidpair, f) = parseSubordPair1 (LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          parseSubord' (f, qidpair::qidpairs)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseSubord' (f as LS.Cons ((L.DOT, _), _), qidpairs) =
          (List.rev qidpairs, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseSubord' (LS.Cons ((t, r), s'), qidpairs) =
          Parsing.error (r, "Expected a pair of identifiers, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)


    fun (* GEN BEGIN FUN FIRST *) parseFreeze' (f as LS.Cons ((L.ID _, _), _), qids) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
        in
          parseFreeze' (f', (ids, name)::qids)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseFreeze' (f as LS.Cons ((L.DOT, _), _), qids) =
          (List.rev qids, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseFreeze' (LS.Cons ((t, r), s'), qids) =
          Parsing.error (r, "Expected identifier, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)

    fun parseThaw' (f, qids) = (* same syntax as %freeze *)
          parseFreeze' (f, qids)

    fun (* GEN BEGIN FUN FIRST *) parseDeterministic' (f as LS.Cons ((L.ID _, _), _), qids) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
        in
          parseDeterministic' (f', (ids, name)::qids)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseDeterministic' (f as LS.Cons ((L.DOT, _), _), qids) =
          (List.rev qids, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseDeterministic' (LS.Cons ((t, r), s'), qids) =
          Parsing.error (r, "Expected identifier, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)

    (* ABP 4/4/03 *)
    fun (* GEN BEGIN FUN FIRST *) parseCompile' (f as LS.Cons ((L.ID _, _), _), qids) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
        in
          parseCompile' (f', (ids, name)::qids)
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseCompile' (f as LS.Cons ((L.DOT, _), _), qids) =
          (List.rev qids, f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseCompile' (LS.Cons ((t, r), s'), qids) =
          Parsing.error (r, "Expected identifier, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)


    (* val parseExp : (L.token * L.region) LS.stream * <p>
                        -> ExtSyn.term * (L.token * L.region) LS.front *)
    fun parseExp (s, p) = parseExp' (LS.expose s, p)

    and (* GEN BEGIN FUN FIRST *) parseExp' (f as LS.Cons((L.ID _, r0), _), p) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((ids, (L.ID (idCase, name), r1)), f') = parseQualId' f (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val r = Paths.join (r0, r1) (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val tm = idToTerm (idCase, ids, name, r) (* GEN END TAG OUTSIDE LET *)
        in
          (* Currently, we cannot override fixity status of identifiers *)
          (* Thus isQuoted always returns false *)
          if isQuoted (idCase)
            then parseExp' (f', P.shiftAtom (tm, p))
          else case Names.fixityLookup (Names.Qid (ids, name))
                 of FX.Nonfix =>
                      parseExp' (f', P.shiftAtom (tm, p))
                  | FX.Infix infixity =>
                      parseExp' (f', P.resolve (r, infixOp (infixity, tm), p))
                  | FX.Prefix (prec) =>
                      parseExp' (f', P.resolve (r, prefixOp (prec, tm), p))
                  | FX.Postfix (prec) =>
                      parseExp' (f', P.resolve (r, postfixOp (prec, tm), p))
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.UNDERSCORE,r), s), p) =
          parseExp (s, P.shiftAtom (ExtSyn.omitted r, p)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.TYPE,r), s), p) =
          parseExp (s, P.shiftAtom (ExtSyn.typ r, p)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.COLON,r), s), p) =
          parseExp (s, P.resolve (r, colonOp, p)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.BACKARROW,r), s), p) =
          parseExp (s, P.resolve (r, backArrowOp, p)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.ARROW,r), s), p) =
          parseExp (s, P.resolve (r, arrowOp, p)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.LPAREN,r), s), p) =
          decideRParen (r, parseExp (s, nil), p) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.RPAREN,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.LBRACE,r), s), p) =
          decideRBrace (r, parseDec (s), p) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.RBRACE,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.LBRACKET,r), s), p) =
          decideRBracket (r, parseDec (s), p) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.RBRACKET,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.EQUAL,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.DOT,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.EOF,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
        (* for some reason, there's no dot after %define decls -kw *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.SOLVE,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (f as LS.Cons((L.DEFINE,r), s), p) =
          (P.reduceAll (r, p), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((L.STRING(str),r), s), p) =
          parseExp (s, P.shiftAtom (ExtSyn.scon (str,r), p)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseExp' (LS.Cons((t,r), s), p) =
          (* possible error recovery: insert DOT *)
          Parsing.error (r, "Unexpected token " ^ L.toString t
                            ^ " found in expression") (* GEN END FUN BRANCH *)

    and parseDec (s) = parseDec' (LS.expose s)
    and (* GEN BEGIN FUN FIRST *) parseDec' (LS.Cons ((L.ID (L.Quoted,name), r), s')) =
          (* cannot happen at present *)
          Parsing.error (r, "Illegal bound quoted identifier " ^ name) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseDec' (LS.Cons ((L.ID (idCase,name), r), s')) =
        (case Names.fixityLookup (Names.Qid (nil, name))
           of FX.Nonfix => parseDec1 (SOME(name), LS.expose s')
            | FX.Infix _ => Parsing.error (r, "Cannot bind infix identifier " ^ name)
            | FX.Prefix _ => Parsing.error (r, "Cannot bind prefix identifier " ^ name)
            | FX.Postfix _ => Parsing.error (r, "Cannot bind postfix identifier " ^ name)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseDec' (LS.Cons ((L.UNDERSCORE, r), s')) =
          parseDec1 (NONE, LS.expose s') (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseDec' (LS.Cons ((L.EOF, r), s')) =
          Parsing.error (r, "Unexpected end of stream in declaration") (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseDec' (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected variable name, found token " ^ L.toString t) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) parseDec1 (x, LS.Cons((L.COLON, r), s')) =
        let (* GEN BEGIN TAG OUTSIDE LET *) val (tm, f'') = parseExp (s', nil) (* GEN END TAG OUTSIDE LET *)
        in ((x, SOME tm), f'') end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseDec1 (x, f as LS.Cons((L.RBRACE, _), _)) =
          ((x, NONE), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseDec1 (x, f as LS.Cons ((L.RBRACKET, _), _)) =
          ((x, NONE), f) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) parseDec1 (x, LS.Cons ((t,r), s')) =
          Parsing.error (r, "Expected optional type declaration, found token "
                            ^ L.toString t) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) decideRParen (r0, (tm, LS.Cons((L.RPAREN,r), s)), p) =
          parseExp (s, P.shiftAtom(tm,p)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decideRParen (r0, (tm, LS.Cons((_, r), s)), p) =
          Parsing.error (Paths.join(r0, r), "Unmatched open parenthesis") (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) decideRBrace (r0, ((x, yOpt), LS.Cons ((L.RBRACE,r), s)), p) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val dec = (case yOpt
                         of NONE => ExtSyn.dec0 (x, Paths.join (r0, r))
                          | SOME y => ExtSyn.dec (x, y, Paths.join (r0, r))) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (tm, f') = parseExp (s, nil) (* GEN END TAG OUTSIDE LET *)
          in
            parseExp' (f', P.shiftAtom (ExtSyn.pi (dec, tm), p))
          end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decideRBrace (r0, (_, LS.Cons ((_, r), s)), p) =
          Parsing.error (Paths.join(r0, r), "Unmatched open brace") (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) decideRBracket (r0, ((x, yOpt), LS.Cons ((L.RBRACKET,r), s)), p) =
          let
            (* GEN BEGIN TAG OUTSIDE LET *) val dec = (case yOpt
                         of NONE => ExtSyn.dec0 (x, Paths.join (r0, r))
                          | SOME y => ExtSyn.dec (x, y, Paths.join (r0, r))) (* GEN END TAG OUTSIDE LET *)
            (* GEN BEGIN TAG OUTSIDE LET *) val (tm, f') = parseExp (s, nil) (* GEN END TAG OUTSIDE LET *)
          in
            parseExp' (f', P.shiftAtom (ExtSyn.lam (dec, tm), p))
          end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) decideRBracket (r0, (dec, LS.Cons ((_, r), s)), p) =
          Parsing.error (Paths.join(r0, r), "Unmatched open bracket") (* GEN END FUN BRANCH *)


    (* Parses contexts of the form  G ::= {id:term} | G, {id:term} *)
    fun (* GEN BEGIN FUN FIRST *) stripRBrace (LS.Cons ((L.RBRACE, r), s')) = (LS.expose s', r) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) stripRBrace (LS.Cons ((t, r), _))  =
          Parsing.error (r, "Expected `}', found " ^ L.toString t) (* GEN END FUN BRANCH *)

    (* parseDec "{id:term} | {id}" *)
    and parseBracedDec (r, f) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val ((x, yOpt), f') = parseDec' f (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val (f'', r2) = stripRBrace f' (* GEN END TAG OUTSIDE LET *)
          (* GEN BEGIN TAG OUTSIDE LET *) val d = (case yOpt
                       of NONE => ExtSyn.dec0 (x, Paths.join (r, r2))
                        | SOME y => ExtSyn.dec (x, y, Paths.join (r, r2))) (* GEN END TAG OUTSIDE LET *)
        in
          (d, f'')
        end

    (* parseCtx (b, ds, f) = ds'
       if   f is a stream "{x1:V1}...{xn:Vn} s"
       and  b is true if no declarations has been parsed yet
       and  ds is a context of declarations
       then ds' = ds, x1:V1, ..., xn:Vn
    *)
    fun (* GEN BEGIN FUN FIRST *) parseCtx (b, ds, LS.Cons (BS as ((L.LBRACE, r), s'))) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val (d, f') = parseBracedDec (r, LS.expose s') (* GEN END TAG OUTSIDE LET *)
        in
          parseCtx (false,  d :: ds, f')
        end (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) parseCtx (b, ds, f as LS.Cons ((t, r), s')) =
        if b then Parsing.error (r, "Expected `{', found " ^ L.toString t)
        else (ds, f) (* GEN END FUN BRANCH *)

  in
    (* GEN BEGIN TAG OUTSIDE LET *) val parseQualId' = parseQualId' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseQualIds' = parseQualIds' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseSubord' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => parseSubord' (f, nil) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseFreeze' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => parseFreeze' (f, nil) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseThaw' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => parseThaw' (f, nil) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseDeterministic' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => parseDeterministic' (f, nil) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseCompile' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => parseCompile' (f, nil) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *) (* -ABP 4/4/03 *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseTerm' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => parseExp' (f, nil) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseDec' = parseDec' (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val parseCtx' = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => (parseCtx (true, nil, f)) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  end  (* local ... in *)

end (* GEN END FUNCTOR DECL *);  (* functor ParseTerm *)
