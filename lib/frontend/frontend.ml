(* Front End Interface *)
(* Author: Frank Pfenning *)

(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
(* Now in lexer.fun *)
(*
module Lexer =
  Lexer (module Stream' = Stream
	 module Paths' = Paths);
*)

(* Now in parsing.fun *)
(*
module Parsing =
  Parsing (module Stream' = Stream
	   module Lexer' = Lexer);
*)


module ReconTerm =
  ReconTerm ((*! module IntSyn' = IntSyn !*)
	     module Names = Names
	     (*! module Paths' = Paths !*)
             module Approx = Approx
 	     module Whnf = Whnf
	     module Unify = UnifyTrail
             module Abstract = Abstract
	     module Print = Print
             (*! module CSManager = CSManager !*)
             module StringTree = StringRedBlackTree
             module Msg = Msg);

module ReconConDec =
  ReconConDec (module Global = Global
               (*! module IntSyn' = IntSyn !*)
               module Names = Names
               module Abstract = Abstract
               (*! module Paths' = Paths !*)
               module ReconTerm' = ReconTerm
               module Constraints = Constraints
               module Strict = Strict
               module TypeCheck = TypeCheck
               module Timers = Timers
               module Print = Print
	       module Msg = Msg);
                                                        
module ReconQuery =
  ReconQuery (module Global = Global
              (*! module IntSyn' = IntSyn !*)
              module Names = Names
              module Abstract = Abstract
              (*! module Paths' = Paths !*)
              module ReconTerm' = ReconTerm
              module TypeCheck = TypeCheck
              module Strict = Strict
              module Timers = Timers
              module Print = Print);

module ReconMode =
  ReconMode (module Global = Global
	     (*! module ModeSyn' = ModeSyn !*)
	     module Whnf = Whnf
	     (*! module Paths' = Paths !*)
             module Names = Names
	     module ModePrint = ModePrint
	     module ModeDec = ModeDec
	     module ReconTerm' = ReconTerm);

module ReconThm =
  ReconThm (module Global = Global
	    module IntSyn = IntSyn
	    module Abstract = Abstract
	    module Constraints = Constraints
	    (*! module ModeSyn = ModeSyn !*)
	    module Names = Names
	    (*! module Paths' = Paths !*)
	    module ThmSyn' = ThmSyn
	    module ReconTerm' = ReconTerm
	    module Print = Print);


module ReconModule =
  ReconModule (module Global = Global
               module IntSyn = IntSyn
               module Names = Names
               (*! module Paths' = Paths !*)
               module ReconTerm' = ReconTerm
               module ModSyn' = ModSyn
               module IntTree = IntRedBlackTree);

module ParseTerm =
  ParseTerm ((*! module Parsing' = Parsing !*)
	     module ExtSyn' = ReconTerm
	     module Names = Names);

module ParseConDec =
  ParseConDec ((*! module Parsing' = Parsing !*)
	       module ExtConDec' = ReconConDec
	       module ParseTerm = ParseTerm);

module ParseQuery =
  ParseQuery ((*! module Parsing' = Parsing !*)
	      module ExtQuery' = ReconQuery
	      module ParseTerm = ParseTerm);

module ParseFixity =
  ParseFixity ((*! module Parsing' = Parsing !*)
	       module Names' = Names);

module ParseMode =
  ParseMode ((*! module Parsing' = Parsing !*)
	     module ExtModes' = ReconMode
	     (*! module Paths = Paths !*)
	     module ParseTerm = ParseTerm);

module ParseThm =
  ParseThm ((*! module Parsing' = Parsing !*)
	    module ThmExtSyn' = ReconThm
	    module ParseTerm = ParseTerm
	    (*! module Paths = Paths !*)
	      );

module ParseModule =
  ParseModule ((*! module Parsing' = Parsing !*)
               module ModExtSyn' = ReconModule
               module ParseTerm = ParseTerm
               (*! module Paths = Paths !*)
		 );

module Parser =
  Parser ((*! module Parsing' = Parsing !*)
	  module Stream' = Stream
	  module ExtSyn' = ReconTerm
	  module Names' = Names
          module ExtConDec' = ReconConDec
          module ExtQuery' = ReconQuery
	  module ExtModes' = ReconMode
	  module ThmExtSyn' = ReconThm
          module ModExtSyn' = ReconModule
	  module ParseConDec = ParseConDec
	  module ParseQuery = ParseQuery
	  module ParseFixity = ParseFixity
	  module ParseMode = ParseMode
	  module ParseThm = ParseThm
          module ParseModule = ParseModule
          module ParseTerm = ParseTerm);

module Solve =
  Solve (module Global = Global
	 (*! module IntSyn' = IntSyn !*)
	 module Names = Names
	 module Parser = Parser
	 module ReconQuery = ReconQuery
	 module Timers = Timers
	 (*! module CompSyn = CompSyn !*)
	 module Compile = Compile
	 module CPrint = CPrint
         (*! module CSManager = CSManager !*)
	 module AbsMachine = SwMachine
	 module PtRecon = PtRecon
	 module AbsMachineSbt = AbsMachineSbt
	 module PtRecon = PtRecon
	 (*! module TableParam = TableParam !*)
	 module Tabled = Tabled
(*	 module TableIndex = TableIndex *)
(*	 module MemoTable = MemoTable *)
	 module Print = Print 
         module Msg = Msg);


module Fquery =
  Fquery (module Global = Global
	  module Names = Names
	  module ReconQuery = ReconQuery
	  module Timers = Timers
	  module Print = Print);

module Twelf =
  Twelf (module Global = Global
	 module Timers = Timers
	 (*! module IntSyn' = IntSyn !*)
	 module Whnf = Whnf
	 module Print = Print

	 module Names = Names
	 (*! module Paths = Paths !*)
	 module Origins = Origins
	 module Lexer = Lexer
	 (*! module Parsing = Parsing !*)
	 module Parser = Parser
	 module TypeCheck = TypeCheck
	 module Strict = Strict
	 module Constraints = Constraints
	 module Abstract = Abstract
	 module ReconTerm = ReconTerm
         module ReconConDec = ReconConDec
         module ReconQuery = ReconQuery

	 module ModeTable = ModeTable
	 module ModeCheck = ModeCheck
	 module ModeDec = ModeDec
	 module ReconMode = ReconMode
	 module ModePrint = ModePrint

         module Unique = Unique
         module UniqueTable = UniqueTable

         module Cover = Cover
	 module Converter = Converter
	 module TomegaPrint = TomegaPrint
	 module TomegaCoverage = TomegaCoverage
	 module TomegaTypeCheck = TomegaTypeCheck
         module Total = Total

	 module Reduces = Reduces

	 module Index = Index
	 module IndexSkolem = IndexSkolem
	 module Subordinate = Subordinate
	 (*! module CompSyn' = CompSyn !*)
	 module Compile = Compile
	 module CPrint = CPrint
	 module AbsMachine = SwMachine
	 (*! module TableParam = TableParam !*)
	 module Tabled = Tabled
	 module Solve = Solve
	 module Fquery = Fquery

	 module StyleCheck = StyleCheck

	 module ThmSyn = ThmSyn
	 module Thm = Thm
	 module ReconThm = ReconThm
	 module ThmPrint = ThmPrint
                              
	 module TabledSyn = TabledSyn

	 module WorldSyn = WorldSyn
(*	 module WorldPrint = WorldPrint *)
	 module Worldify = Worldify

         module ModSyn = ModSyn
         module ReconModule = ReconModule

	 module MetaGlobal = MetaGlobal
	 (*! module FunSyn = FunSyn !*)
	 module Skolem = Skolem
	 module Prover = CombiProver
	 module ClausePrint = ClausePrint

         module Trace = Trace

	 module PrintTeX = PrintTeX
	 module ClausePrintTeX = ClausePrintTeX

         module CSManager = CSManager
         module CSInstaller = CSInstaller (* unused -- creates necessary CM dependency *)

         module Compat = Compat
	 module UnknownExn = UnknownExn

	 module Msg = Msg
	   );
