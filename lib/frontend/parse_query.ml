open Basis
(* Parsing Queries *)

(* Author: Frank Pfenning *)

module type PARSE_QUERY = sig
  (*! structure Parsing : Parsing.PARSING !*)
  module ExtQuery : Recon_query.EXTQUERY

  val parseQuery' : ExtQuery.query Parsing.parser
  val parseSolve' : ExtQuery.define list * ExtQuery.solve Parsing.parser
end

(* signature Parse_prg.PARSE_QUERY *)
(* Parsing Queries *)

(* Author: Frank Pfenning *)

module ParseQuery
    (ExtQuery' : Recon_query.EXTQUERY)
    (ParseTerm : Parse_prg.Parse_term.PARSE_TERM) : Parse_prg.PARSE_QUERY =
struct
  (*! structure Parsing = Parsing' !*)

  module ExtQuery = ExtQuery'
  module L = Lexer
  module LS = LexerStream
  module P = Paths

  let rec returnQuery (optName, (tm, f)) = (ExtQuery.query (optName, tm), f)
  (* parseQuery1 (name, f, f')   ": A" from f' or "V" from f. *)

  let rec parseQuery1 = function
    | name, f, LS.Cons ((L.COLON, r), s') ->
        returnQuery (Some name, ParseTerm.parseTerm' (LS.expose s'))
    | name, f, _ -> returnQuery (None, ParseTerm.parseTerm' f)
  (* parseQuery' : lexResult front -> ExtQuery.query * lexResult front *)

  (* parseQuery'  "X : A" | "A" *)

  (* Query parsing is ambiguous, since a term "V" might have the form "U' : V'" *)

  (* We look for_sml an uppercase variable X followed by a `:'.
       If we find this, we parse a query of the form "X : A".
       Otherwise we parse a query of the form "A".
    *)

  let rec parseQuery' = function
    | f -> parseQuery1 (name, f, LS.expose s')
    | f -> returnQuery (None, ParseTerm.parseTerm' f)
  (* parseQuery --- currently not exported *)

  let rec parseQuery s = parseQuery' (LS.expose s)
  (* parseDefine4 parses the definition body *)

  (* "U" *)

  let rec parseDefine4 (optName, optT, s) =
    let tm', f' = ParseTerm.parseTerm' (LS.expose s) in
    (ExtQuery.define (optName, tm', optT), f')
  (* parseDefine3 parses the equal sign in a long form define *)

  (* "= U" *)

  let rec parseDefine3 = function
    | optName, (tm, LS.Cons ((L.Eq, r), s')) ->
        parseDefine4 (optName, Some tm, s')
    | _, (tm, LS.Cons ((t, r), _)) ->
        Parsing.error (r, "Expected `=', found " ^ L.toString t)
  (* parseDefine2 switches between short and long form *)

  (* ": V = U" | "= U" *)

  let rec parseDefine2 = function
    | optName, LS.Cons ((L.COLON, r), s') ->
        parseDefine3 (optName, ParseTerm.parseTerm' (LS.expose s'))
    | optName, LS.Cons ((L.Eq, r), s') -> parseDefine4 (optName, None, s')
    | _, LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)
  (* parseDefine1 parses the name of the constant to be defined *)

  (* "c : V = U" | "_ : V = U" | "c = U" | "_ = U" *)

  let rec parseDefine1 = function
    | LS.Cons ((L.ID (idCase, name), r), s') ->
        parseDefine2 (Some name, LS.expose s')
    | LS.Cons ((L.UNDERSCORE, r), s') -> parseDefine2 (None, LS.expose s')
    | LS.Cons ((t, r), _) ->
        Parsing.error (r, "Expected identifier or `_', found " ^ L.toString t)

  let rec parseSolve3 = function
    | defns, nameOpt, LS.Cons ((L.COLON, r), s'), r0 ->
        let tm, f' = ParseTerm.parseTerm' (LS.expose s') in
        ((List.rev defns, ExtQuery.solve (nameOpt, tm, P.join (r0, r))), f')
    | _, _, LS.Cons ((t, r), s'), r0 ->
        Parsing.error (r, "Expected `:', found " ^ L.toString t)

  let rec parseSolve2 = function
    | defns, LS.Cons ((L.UNDERSCORE, r), s'), r0 ->
        parseSolve3 (defns, None, LS.expose s', r0)
    | defns, LS.Cons ((L.ID (_, name), r), s'), r0 ->
        parseSolve3 (defns, Some name, LS.expose s', r0)
    | _, LS.Cons ((t, r), s'), r0 ->
        Parsing.error (r, "Expected identifier or `_', found " ^ L.toString t)

  and parseSolve1 = function
    | defns, LS.Cons ((L.Solve.SOLVE, r0), s') ->
        parseSolve2 (defns, LS.expose s', r0)
    | defns, LS.Cons ((L.DEFINE, r0), s') ->
        let defn, f' = parseDefine1 (LS.expose s') in
        parseSolve1 (defn :: defns, f')
    | defns, LS.Cons ((t, r), s) ->
        Parsing.error (r, "Expected %define or %solve, found " ^ L.toString t)

  and parseSolve' f = parseSolve1 ([], f)

  let parseQuery' = parseQuery'
  let parseSolve' = parseSolve'
  (* local ... in *)
end

(* functor ParseQuery *)
