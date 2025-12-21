module MTPGlobal = MTPGlobal (struct
  module MetaGlobal = MetaGlobal
end)

(* Now in funsyn.fun *)

(*
structure FunSyn = 
  FunSyn ((*! structure IntSyn' = IntSyn !*)
	  structure Whnf = Whnf
	  structure Conv = Conv);
*)

module StateSyn =
  StateSyn
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Conv = Conv
    end)

module FunNames =
  FunNames
    (struct
      module Global = Global
    end)
    (struct
      module HashTable = StringHashTable
    end)

module FunPrint =
  FunPrint
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Names = Names
    end)

(* moves eventually into the Twelf core *)

module Weaken = Weaken (struct
  module Whnf = Whnf
end)

module FunWeaken = FunWeaken (struct
  module Weaken = Weaken
end)

module FunTypeCheck =
  FunTypeCheck
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module Weaken = Weaken
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module FunPrint = FunPrint
    end)

module RelFun =
  RelFun
    (struct
      module Global = Global
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module Names = Names
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Trail = Trail
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Weaken = Weaken
    end)
    (struct
      module FunWeaken = FunWeaken
    end)
    (struct
      module FunNames = FunNames
    end)

(* Functor instantiation for_sml the Prover *)

module MTPData = MTPData (struct
  module MTPGlobal = MTPGlobal
end)

module MTPAbstract =
  MTPAbstract
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Constraints = Constraints
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module FunTypeCheck = FunTypeCheck
    end)
    (struct
      module Abstract = Abstract
    end)

module MTPInit =
  MTPInit
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module Names = Names
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module MTPData = MTPData
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module FunPrint = FunPrint
    end)

module MTPrint =
  MTPrint
    (struct
      module Global = Global
    end)
    (struct
      module Names = Names
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module Formatter' = Formatter
    end)
    (struct
      module Print = Print
    end)
    (struct
      module FunPrint = FunPrint
    end)

module MTPSearch =
  MTPSearch
    (struct
      module Global = Global
    end)
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module StateSyn' = StateSyn
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

module MTPFilling =
  MTPFilling
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module MTPData = MTPData
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Search = MTPSearch
    end)
    (struct
      module Whnf = Whnf
    end)

module MTPSplitting =
  MTPSplitting
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module Global = Global
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module Heuristic = Heuristic
    end)
    (struct
      module MTPrint = MTPrint
    end)
    (struct
      module MTPAbstract = MTPAbstract
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module FunTypeCheck = FunTypeCheck
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

module UniqueSearch =
  UniqueSearch
    (struct
      module Global = Global
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module Assign = Assign
    end)
    (struct
      module Index = Index
    end)
    (struct
      module Compile = Compile
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

module Inference =
  Inference
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module FunTypeCheck = FunTypeCheck
    end)
    (struct
      module UniqueSearch = UniqueSearch
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)

module MTPRecursion =
  MTPRecursion
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module Global = Global
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module FunTypeCheck = FunTypeCheck
    end)
    (struct
      module MTPSearch = MTPSearch
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module MTPAbstract = MTPAbstract
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
      module Subordinate = Subordinate
    end)
    (struct
      module MTPrint = MTPrint
    end)
    (struct
      module Print = Print
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module FunPrint = FunPrint
    end)
    (struct
      module Formatter = Formatter
    end)

module MTPStrategy =
  MTPStrategy
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module MTPrint = MTPrint
    end)
    (struct
      module MTPData = MTPData
    end)
    (struct
      module MTPFilling = MTPFilling
    end)
    (struct
      module MTPSplitting = MTPSplitting
    end)
    (struct
      module MTPRecursion = MTPRecursion
    end)
    (struct
      module Inference = Inference
    end)
    (struct
      module Timers = Timers
    end)

module MTProver =
  MTProver
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module StateSyn = StateSyn
    end)
    (struct
      module Order = Order
    end)
    (struct
      module MTPrint = MTPrint
    end)
    (struct
      module MTPInit = MTPInit
    end)
    (struct
      module MTPStrategy = MTPStrategy
    end)
    (struct
      module RelFun = RelFun
    end)

module CombiProver =
  CombiProver
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module ProverNew = MTProver
    end)
    (struct
      module ProverOld = Prover
    end)

module MTPi =
  MTPi
    (struct
      module MTPGlobal = MTPGlobal
    end)
    (struct
      module StateSyn' = StateSyn
    end)
    (struct
      module FunTypeCheck = FunTypeCheck
    end)
    (struct
      module RelFun = RelFun
    end)
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Print = Print
    end)
    (struct
      module MTPrint = MTPrint
    end)
    (struct
      module MTPInit = MTPInit
    end)
    (struct
      module MTPFilling = MTPFilling
    end)
    (struct
      module MTPData = MTPData
    end)
    (struct
      module MTPSplitting = MTPSplitting
    end)
    (struct
      module MTPRecursion = MTPRecursion
    end)
    (struct
      module Inference = Inference
    end)
    (struct
      module MTPStrategy = MTPStrategy
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Order = Order
    end)
    (struct
      module Timers = Timers
    end)
    (struct
      module Ring = Ring
    end)
