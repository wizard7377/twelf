(* Front End Interface *)

(* Author: Frank Pfenning *)

(* Presently, we do not memoize the token stream returned *)

(* by the lexer.  Use Stream = MStream below if memoization becomes *)

(* necessary. *)

(* Now in lexer.fun *)

(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)

(* Now in parsing.fun *)

(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)

module ReconTerm =
  ReconTerm
    (struct
      module Names = Names
    end)
    (struct
      module Approx = Approx
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Print = Print
    end)
    (struct
      module StringTree = StringRedBlackTree
    end)
    (struct
      module Msg = Msg
    end)

module ReconConDec =
  ReconConDec
    (struct
      module Global = Global
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module ReconTerm' = ReconTerm
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Strict = Strict
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Msg = Msg
    end)

module ReconQuery =
  ReconQuery
    (struct
      module Global = Global
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module ReconTerm' = ReconTerm
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Strict = Strict
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Print = Print
    end)

module ReconMode =
  ReconMode
    (struct
      module Global = Global
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Names = Names
    end)
    (struct
      module ModePrint = ModePrint
    end)
    (struct
      module ModeDec = ModeDec
    end)
    (struct
      module ReconTerm' = ReconTerm
    end)

module ReconThm =
  ReconThm
    (struct
      module Global = Global
    end)
    (struct
      module IntSyn = IntSyn
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Names = Names
    end)
    (struct
      module ThmSyn' = ThmSyn
    end)
    (struct
      module ReconTerm' = ReconTerm
    end)
    (struct
      module Print = Print
    end)

module ReconModule =
  ReconModule
    (struct
      module Global = Global
    end)
    (struct
      module IntSyn = IntSyn
    end)
    (struct
      module Names = Names
    end)
    (struct
      module ReconTerm' = ReconTerm
    end)
    (struct
      module ModSyn' = ModSyn
    end)
    (struct
      module IntTree = IntRedBlackTree
    end)

module ParseTerm =
  ParseTerm
    (struct
      module ExtSyn' = ReconTerm
    end)
    (struct
      module Names = Names
    end)

module ParseConDec =
  ParseConDec
    (struct
      module ExtConDec' = ReconConDec
    end)
    (struct
      module ParseTerm = ParseTerm
    end)

module ParseQuery =
  ParseQuery
    (struct
      module ExtQuery' = ReconQuery
    end)
    (struct
      module ParseTerm = ParseTerm
    end)

module ParseFixity = ParseFixity (struct
  module Names' = Names
end)

module ParseMode =
  ParseMode
    (struct
      module ExtModes' = ReconMode
    end)
    (struct
      module ParseTerm = ParseTerm
    end)

module ParseThm =
  ParseThm
    (struct
      module ThmExtSyn' = ReconThm
    end)
    (struct
      module ParseTerm = ParseTerm
    end)

module ParseModule =
  ParseModule
    (struct
      module ModExtSyn' = ReconModule
    end)
    (struct
      module ParseTerm = ParseTerm
    end)

module Parser =
  Parser
    (struct
      module Stream' = Stream
    end)
    (struct
      module ExtSyn' = ReconTerm
    end)
    (struct
      module Names' = Names
    end)
    (struct
      module ExtConDec' = ReconConDec
    end)
    (struct
      module ExtQuery' = ReconQuery
    end)
    (struct
      module ExtModes' = ReconMode
    end)
    (struct
      module ThmExtSyn' = ReconThm
    end)
    (struct
      module ModExtSyn' = ReconModule
    end)
    (struct
      module ParseConDec = ParseConDec
    end)
    (struct
      module ParseQuery = ParseQuery
    end)
    (struct
      module ParseFixity = ParseFixity
    end)
    (struct
      module ParseMode = ParseMode
    end)
    (struct
      module ParseThm = ParseThm
    end)
    (struct
      module ParseModule = ParseModule
    end)
    (struct
      module ParseTerm = ParseTerm
    end)

module Solve =
  Solve
    (struct
      module Global = Global
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Parser = Parser
    end)
    (struct
      module ReconQuery = ReconQuery
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Compile = Compile
    end)
    (struct
      module CPrint = CPrint
    end)
    (struct
      module AbsMachine = SwMachine
    end)
    (struct
      module PtRecon = PtRecon
    end)
    (struct
      module AbsMachineSbt = AbsMachineSbt
    end)
    (struct
      module PtRecon = PtRecon
    end)
    (struct
      module Tabled = Tabled
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Msg = Msg
    end)

module Fquery =
  Fquery
    (struct
      module Global = Global
    end)
    (struct
      module Names = Names
    end)
    (struct
      module ReconQuery = ReconQuery
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Print = Print
    end)

module Twelf =
  Twelf
    (struct
      module Global = Global
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Origins = Origins
    end)
    (struct
      module Lexer = Lexer
    end)
    (struct
      module Parser = Parser
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Strict = Strict
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module ReconTerm = ReconTerm
    end)
    (struct
      module ReconConDec = ReconConDec
    end)
    (struct
      module ReconQuery = ReconQuery
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module ModeCheck = ModeCheck
    end)
    (struct
      module ModeDec = ModeDec
    end)
    (struct
      module ReconMode = ReconMode
    end)
    (struct
      module ModePrint = ModePrint
    end)
    (struct
      module Unique = Unique
    end)
    (struct
      module UniqueTable = UniqueTable
    end)
    (struct
      module Cover = Cover
    end)
    (struct
      module Converter = Converter
    end)
    (struct
      module TomegaPrint = TomegaPrint
    end)
    (struct
      module TomegaCoverage = TomegaCoverage
    end)
    (struct
      module TomegaTypeCheck = TomegaTypeCheck
    end)
    (struct
      module Total = Total
    end)
    (struct
      module Reduces = Reduces
    end)
    (struct
      module Index = Index
    end)
    (struct
      module IndexSkolem = IndexSkolem
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module Compile = Compile
    end)
    (struct
      module CPrint = CPrint
    end)
    (struct
      module AbsMachine = SwMachine
    end)
    (struct
      module Tabled = Tabled
    end)
    (struct
      module Solve = Solve
    end)
    (struct
      module Fquery = Fquery
    end)
    (struct
      module StyleCheck = StyleCheck
    end)
    (struct
      module ThmSyn = ThmSyn
    end)
    (struct
      module Thm = Thm
    end)
    (struct
      module ReconThm = ReconThm
    end)
    (struct
      module ThmPrint = ThmPrint
    end)
    (struct
      module TabledSyn = TabledSyn
    end)
    (struct
      module WorldSyn = WorldSyn
    end)
    (struct
      module Worldify = Worldify
    end)
    (struct
      module ModSyn = ModSyn
    end)
    (struct
      module ReconModule = ReconModule
    end)
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module Skolem = Skolem
    end)
    (struct
      module Prover = CombiProver
    end)
    (struct
      module ClausePrint = ClausePrint
    end)
    (struct
      module Trace = Trace
    end)
    (struct
      module PrintTeX = PrintTeX
    end)
    (struct
      module ClausePrintTeX = ClausePrintTeX
    end)
    (struct
      module CSManager = Cs.CSManager
    end)
    (struct
      module CSInstaller = Cs.CSInstaller
    end)
    (struct
      module Compat = Compat
    end)
    (struct
      module UnknownExn = UnknownExn
    end)
    (struct
      module Msg = Msg
    end)
