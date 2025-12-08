(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: not supported by cvs2svn $
 * Revision 1.1.2.1  2003/01/14 22:46:39  carsten_lf
 * delphin frontend added
 *
 * Revision 1.1  2001/11/12 23:23:09  carsten
 * mlyacc hack included
 *
 * Revision 1.1.1.1  1999/12/03 19:59:22  dbm
 * Import of 110.0.6 src
 *
 * Revision 1.1.1.1  1997/01/14 01:38:04  george
 *   Version 109.24
 *
 * Revision 1.1.1.1  1996/01/31  16:01:42  george
 * Version 109
 * 
 *)

(* base.sig: Base module type file for SML-Yacc.  This file contains signatures
   that must be loaded before any of the files produced by ML-Yacc are loaded
*)

(* STREAM: module type for a lazy stream.*)

module type STREAMM =
 sig type 'xa stream
     let streamify : (unit -> '_a) -> '_a stream
     let cons : '_a * '_a stream -> '_a stream
     let get : '_a stream -> '_a * '_a stream
 end

(* LR_TABLE: module type for an LR Table.

   The list of actions and gotos passed to mkLrTable must be ordered by state
   number. The values for state 0 are the first in the list, the values for
    state 1 are next, etc.
*)

module type LR_TABLE =
    sig
        type ('a,'b) pairlist = EMPTY | PAIR of 'a * 'b * ('a,'b) pairlist
	type state = STATE of int
	type term = T of int
	type nonterm = NT of int
	type action = SHIFT of state
			| REDUCE of int
			| ACCEPT
			| ERROR
	type table
	
	let numStates : table -> int
	let numRules : table -> int
	let describeActions : table -> state ->
				(term,action) pairlist * action
	let describeGoto : table -> state -> (nonterm,state) pairlist
	let action : table -> state * term -> action
	let goto : table -> state * nonterm -> state
	let initialState : table -> state
	exception Goto of state * nonterm

	let mkLrTable : {actions : ((term,action) pairlist * action) array,
			 gotos : (nonterm,state) pairlist array,
			 numStates : int, numRules : int,
			 initialState : state} -> table
    end

(* TOKEN: module type revealing the internal module of a token. This module type
   TOKEN distinct from the module type {parser name}_TOKENS produced by ML-Yacc.
   The {parser name}_TOKENS structures contain some types and functions to
    construct tokens from values and positions.

   The representation of token was very carefully chosen here to allow the
   polymorphic parser to work without knowing the types of semantic values
   or line numbers.

   This has had an impact on the TOKENS module produced by SML-Yacc, which
   is a module parameter to lexer functors.  We would like to have some
   type 'a token which functions to construct tokens would create.  A
   constructor function for a integer token might be

	  INT: int * 'a * 'a -> 'a token.
 
   This is not possible because we need to have tokens with the representation
   given below for the polymorphic parser.

   Thus our constructur functions for tokens have the form:

	  INT: int * 'a * 'a -> (svalue,'a) token

   This in turn has had an impact on the module type that lexers for SML-Yacc
   must match and the types that a user must declare in the user declarations
   section of lexers.
*)

module type TOKEN =
    sig
	(LrTable : LR_TABLE)
        type ('a,'b) token = TOKEN of LrTable.term * ('a * 'b * 'b)
	let sameToken : ('a,'b) token * ('a,'b) token -> bool
    end

(* LR_PARSER: module type for a polymorphic LR parser *)

module type LR_PARSER =
    sig
	module Streamm: STREAMM
	(LrTable : LR_TABLE)
	(Token : TOKEN)

	sharing LrTable = Token.LrTable

	exception ParseError

	let parse : {table : LrTable.table,
		     lexer : ('_b,'_c) Token.token Streamm.stream,
		     arg: 'arg,
		     saction : int *
			       '_c *
				(LrTable.state * ('_b * '_c * '_c)) list * 
				'arg ->
				     LrTable.nonterm *
				     ('_b * '_c * '_c) *
				     ((LrTable.state *('_b * '_c * '_c)) list),
		     void : '_b,
		     ec : { is_keyword : LrTable.term -> bool,
			    noShift : LrTable.term -> bool,
			    preferred_change : (LrTable.term list * LrTable.term list) list,
			    errtermvalue : LrTable.term -> '_b,
			    showTerminal : LrTable.term -> string,
			    terms: LrTable.term list,
			    error : string * '_c * '_c -> unit
			   },
		     lookahead : int  (* max amount of lookahead used in *)
				      (* error correction *)
			} -> '_b *
			     (('_b,'_c) Token.token Streamm.stream)
    end

(* LEXERR: a module type that most lexers produced for use with SML-Yacc's
   output will match.  The user is responsible for declaring type token,
   type pos, and type svalue in the UserDeclarations section of a lexer.

   Note that type token is abstract in the lexer.  This allows SML-Yacc to
   create a TOKENS module type for use with lexers produced by ML-Lex that
   treats the type token abstractly.  Lexers that are functors parametrized by
   a Tokens module matching a TOKENS module type cannot examine the module
   of tokens.
*)

module type LEXERR =
   sig
       module UserDeclarations :
	   sig
	        type ('a,'b) token
		type pos
		type svalue
	   end
	let makeLexer : (int -> string) -> unit -> 
         (UserDeclarations.svalue,UserDeclarations.pos) UserDeclarations.token
   end

(* ARG_LEXER: the %arg option of ML-Lex allows users to produce lexers which
   also take an argument before yielding a function from unit to a token
*)

module type ARG_LEXER =
   sig
       module UserDeclarations :
	   sig
	        type ('a,'b) token
		type pos
		type svalue
		type arg
	   end
	let makeLexer : (int -> string) -> UserDeclarations.arg -> unit -> 
         (UserDeclarations.svalue,UserDeclarations.pos) UserDeclarations.token
   end

(* PARSER_DATA: the module type of ParserData structures in {parser name}LrValsFun
   produced by  SML-Yacc.  All such structures match this module type.  

   The {parser name}LrValsFun produces a module which contains all the values
   except for the lexer needed to call the polymorphic parser mentioned
   before.

*)

module type PARSER_DATA =
   sig
        (* the type of line numbers *)

	type pos

	(* the type of semantic values *)

	type svalue

         (* the type of the user-supplied argument to the parser *)
 	type arg
 
	(* the intended type of the result of the parser.  This value is
	   produced by applying extract from the module Actions to the
	   final semantic value resultiing from a parse.
	 *)

	type result

	(LrTable : LR_TABLE)
	(Token : TOKEN)
	sharing Token.LrTable = LrTable

	(* module Actions contains the functions which mantain the
	   semantic values stack in the parser.  Void is used to provide
	   a default value for the semantic stack.
	 *)

	module Actions : 
	  sig
	      let actions : int * pos *
		   (LrTable.state * (svalue * pos * pos)) list * arg->
		         LrTable.nonterm * (svalue * pos * pos) *
			 ((LrTable.state *(svalue * pos * pos)) list)
	      let void : svalue
	      let extract : svalue -> result
	  end

	(* module EC contains information used to improve error
	   recovery in an error-correcting parser *)

	module EC :
	   sig
	     let is_keyword : LrTable.term -> bool
	     let noShift : LrTable.term -> bool
 	     let preferred_change : (LrTable.term list * LrTable.term list) list
	     let errtermvalue : LrTable.term -> svalue
	     let showTerminal : LrTable.term -> string
	     let terms: LrTable.term list
	   end

	(* table is the LR table for the parser *)

	let table : LrTable.table
    end

(* module type PARSER is the module type that most user parsers created by 
   SML-Yacc will match.
*)

module type PARSERR =
    sig
        (Token : TOKEN)
	(Streamm : STREAMM)
	exception ParseError

	(* type pos is the type of line numbers *)

	type pos

	(* type result is the type of the result from the parser *)

	type result

         (* the type of the user-supplied argument to the parser *)
 	type arg
	
	(* type svalue is the type of semantic values for the semantic value
	   stack
	 *)

	type svalue

	(* let makeLexer is used to create a stream of tokens for the parser *)

	let makeLexer : (int -> string) ->
			 (svalue,pos) Token.token Streamm.stream

	(* let parse takes a stream of tokens and a function to print
	   errors and returns a value of type result and a stream containing
	   the unused tokens
	 *)

	let parse : int * ((svalue,pos) Token.token Streamm.stream) *
		    (string * pos * pos -> unit) * arg ->
				result * (svalue,pos) Token.token Streamm.stream

	let sameToken : (svalue,pos) Token.token * (svalue,pos) Token.token ->
				bool
     end

(* module type ARG_PARSER is the module type that will be matched by parsers whose
    lexer takes an additional argument.
*)

module type ARG_PARSER = 
    sig
        (Token : TOKEN)
	(Streamm : STREAMM)
	exception ParseError

	type arg
	type lexarg
	type pos
	type result
	type svalue

	let makeLexer : (int -> string) -> lexarg ->
			 (svalue,pos) Token.token Streamm.stream
	let parse : int * ((svalue,pos) Token.token Streamm.stream) *
		    (string * pos * pos -> unit) * arg ->
				result * (svalue,pos) Token.token Streamm.stream

	let sameToken : (svalue,pos) Token.token * (svalue,pos) Token.token ->
				bool
     end

