open Basis

module MetaSyn = MetaSyn (struct
  module Whnf = Whnf
end)

module MetaAbstract =
  MetaAbstract
    (struct
      module Global = Global
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Unify = UnifyNoTrail
    end)
    (struct
      module Names = Names
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Subordinate = Subordinate
    end)

module MetaPrint =
  MetaPrint
    (struct
      module Global = Global
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Print = Print
    end)
    (struct
      module ClausePrint = ClausePrint
    end)

module Init =
  Init
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)

module OLDSearch =
  OLDSearch
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module Compile = Compile
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Index = IndexSkolem
    end)
    (struct
      module CPrint = CPrint
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Names = Names
    end)

module Lemma =
  Lemma
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)

module Splitting =
  Splitting
    (struct
      module Global = Global
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaPrint = MetaPrint
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Unify = UnifyTrail
    end)

module Filling =
  Filling
    (struct
      module Global = Global
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Search = OLDSearch
    end)
    (struct
      module Whnf = Whnf
    end)

module Recursion =
  Recursion
    (struct
      module Global = Global
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaPrint = MetaPrint
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module Order = Order
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module Lemma = Lemma
    end)
    (struct
      module Filling = Filling
    end)
    (struct
      module Formatter = Formatter
    end)

module Qed =
  Qed
    (struct
      module Global = Global
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)

module StrategyFRS =
  StrategyFRS
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module Lemma = Lemma
    end)
    (struct
      module Filling = Filling
    end)
    (struct
      module Recursion = Recursion
    end)
    (struct
      module Splitting = Splitting
    end)
    (struct
      module Qed = Qed
    end)
    (struct
      module MetaPrint = MetaPrint
    end)
    (struct
      module Timers = Timers
    end)

module StrategyRFS =
  StrategyRFS
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module Lemma = Lemma
    end)
    (struct
      module Filling = Filling
    end)
    (struct
      module Recursion = Recursion
    end)
    (struct
      module Splitting = Splitting
    end)
    (struct
      module Qed = Qed
    end)
    (struct
      module MetaPrint = MetaPrint
    end)
    (struct
      module Timers = Timers
    end)

module Strategy =
  Strategy
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module StrategyFRS = StrategyFRS
    end)
    (struct
      module StrategyRFS = StrategyRFS
    end)

module Prover =
  Prover
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module MetaPrint = MetaPrint
    end)
    (struct
      module Filling = Filling
    end)
    (struct
      module Splitting = Splitting
    end)
    (struct
      module Recursion = Recursion
    end)
    (struct
      module Init = Init
    end)
    (struct
      module Strategy = Strategy
    end)
    (struct
      module Qed = Qed
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Timers = Timers
    end)

module Mpi =
  Mpi
    (struct
      module MetaGlobal = MetaGlobal
    end)
    (struct
      module MetaSyn' = MetaSyn
    end)
    (struct
      module MetaAbstract = MetaAbstract
    end)
    (struct
      module Init = Init
    end)
    (struct
      module Lemma = Lemma
    end)
    (struct
      module Filling = Filling
    end)
    (struct
      module Recursion = Recursion
    end)
    (struct
      module Splitting = Splitting
    end)
    (struct
      module Strategy = Strategy
    end)
    (struct
      module Qed = Qed
    end)
    (struct
      module MetaPrint = MetaPrint
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Ring = Ring
    end)

module Skolem =
  Skolem
    (struct
      module Global = Global
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module IndexSkolem = IndexSkolem
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Compile = Compile
    end)
    (struct
      module Names = Names
    end)
