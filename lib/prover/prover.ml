module State =
  State
    (struct
      module WorldSyn' = WorldSyn
    end)
    (struct
      module Formatter = Formatter
    end)

module Introduce =
  Introduce
    (struct
      module TomegaNames = TomegaNames
    end)
    (struct
      module State' = State
    end)

module Elim =
  Elim
    (struct
      module Data = Data
    end)
    (struct
      module State' = State
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Index = Index
    end)
    (struct
      module TypeCheck = TypeCheck
    end)

module FixedPoint = FixedPoint (struct
  module State' = State
end)

module Split =
  Split
    (struct
      module Global = Global
    end)
    (struct
      module State' = State
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Print = Print
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Subordinate = Subordinate
    end)

module Search =
  Search
    (struct
      module Global = Global
    end)
    (struct
      module Data = Data
    end)
    (struct
      module State' = State
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module CompSyn' = CompSyn
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
      module Assign = Assign
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
    (struct
      module CSManager = Cs.CSManager
    end)

module Fill =
  Fill
    (struct
      module Data = Data
    end)
    (struct
      module State' = State
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Search = Search
    end)
    (struct
      module TypeCheck = TypeCheck
    end)

module Weaken = Weaken (struct
  module Whnf = Whnf
end)

(*
structure Recurse = Recurse
  (structure Global = Global
   structure Data = Data
   structure State' = State
   structure Whnf = Whnf
   structure Conv = Conv
   structure Names = Names
   structure Subordinate = Subordinate
   structure Print = Print
   structure Formatter = Formatter
   structure TomegaPrint = TomegaPrint
   structure Abstract = Abstract
   structure Unify = UnifyTrail
   structure Constraints = Constraints
   structure Index = Index
   structure Search = Search
   structure TypeCheck = TypeCheck)
*)

module Interactive =
  Interactive
    (struct
      module Global = Global
    end)
    (struct
      module State' = State
    end)
    (struct
      module Ring = Ring
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Trail = Trail
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Weaken = Weaken
    end)
    (struct
      module ModeSyn = ModeSyn
    end)
    (struct
      module WorldSyn = WorldSyn
    end)
    (struct
      module Introduce = Introduce
    end)
    (struct
      module FixedPoint = FixedPoint
    end)
    (struct
      module Split = Split
    end)
    (struct
      module Fill = Fill
    end)
    (struct
      module Elim = Elim
    end)
