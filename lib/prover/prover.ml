module State = State 
  ((*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module WorldSyn' = WorldSyn
   module Formatter = Formatter)
     
module Introduce = Introduce 
  ((*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module TomegaNames = TomegaNames
   module State' = State)

   
module Elim = Elim 
  (module Data = Data
   (*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module State' = State
   module Whnf = Whnf
   module Abstract = Abstract
   module Unify = UnifyTrail
   module Constraints = Constraints
   module Index = Index
   module TypeCheck = TypeCheck)
 
module FixedPoint = FixedPoint 
  ((*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module State' = State)

module Split = Split
  (module Global = Global
   (*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module State' = State
   module Whnf = Whnf
   module Abstract = Abstract
   module Unify = UnifyTrail
   module Constraints = Constraints
   module Index = Index
   module Names = Names
   module Print = Print
   module TypeCheck = TypeCheck
   module Subordinate = Subordinate)


module Search = Search 
  (module Global = Global
   module Data = Data
   (*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module State' = State
   module Abstract = Abstract
   module Conv = Conv
   module CompSyn' = CompSyn
   module Compile = Compile
   module Whnf = Whnf
   module Unify = UnifyTrail
   module Index = IndexSkolem
   module Assign = Assign 
   module CPrint = CPrint
   module Print = Print
   module Names = Names
   module CSManager = CSManager); 

module Fill = Fill
  (module Data = Data
   (*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module State' = State
   module Whnf = Whnf
   module Abstract = Abstract
   module Unify = UnifyTrail
   module Constraints = Constraints
   module Index = Index
   module Search = Search
   module TypeCheck = TypeCheck)

module Weaken =
  Weaken ((*! module IntSyn' = IntSyn !*)
	  module Whnf = Whnf)

(*
module Recurse = Recurse
  (module Global = Global
   module Data = Data
   module State' = State
   module Whnf = Whnf
   module Conv = Conv
   module Names = Names
   module Subordinate = Subordinate
   module Print = Print
   module Formatter = Formatter
   module TomegaPrint = TomegaPrint
   module Abstract = Abstract
   module Unify = UnifyTrail
   module Constraints = Constraints
   module Index = Index
   module Search = Search
   module TypeCheck = TypeCheck)
*)


module Interactive = Interactive
  (module Global = Global
   (*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module State' = State
   module Ring = Ring
   module Formatter = Formatter
   module Trail = Trail
   module Names = Names
   module Weaken = Weaken
   module ModeSyn = ModeSyn
   module WorldSyn = WorldSyn
   module Introduce = Introduce
   module FixedPoint = FixedPoint
   module Split = Split
   module Fill = Fill
   module Elim = Elim)
 