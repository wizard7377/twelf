module TomegaAbstract =
  TomegaAbstract
    (struct
      module Global = Global
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Subordinate = Subordinate
    end)

module TomegaPrint =
  TomegaPrint
    (struct
      module Formatter = Formatter
    end)
    (struct
      module Names = Names
    end)
    (struct
      module Print = Print
    end)

module TomegaTypeCheck =
  TomegaTypeCheck
    (struct
      module Global = Global
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
      module Whnf = Whnf
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module TomegaPrint = TomegaPrint
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Weaken = Weaken
    end)
    (struct
      module TomegaAbstract = TomegaAbstract
    end)

(* structure TomegaUnify = TomegaUnify
  (structure Global = Global
   (*! structure IntSyn' = IntSyn !*)
   structure Abstract = Abstract
   (*! structure Tomega' = Tomega !*)
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken);
*)

module Opsem =
  Opsem
    (struct
      module Global = Global
    end)
    (struct
      module IntSyn' = IntSyn
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Tomega' = Tomega
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module Unify = UnifyNoTrail
    end)
    (struct
      module Conv = Conv
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module TomegaPrint = TomegaPrint
    end)
    (struct
      module TomegaTypeCheck = TomegaTypeCheck
    end)
    (struct
      module Weaken = Weaken
    end)

(*
structure Opsem = OpsemCont
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Unify = UnifyNoTrail
   structure Conv = Conv
   structure Whnf = Whnf
   structure Print = Print
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Weaken = Weaken);
*)

module Redundant = Redundant (struct
  module Opsem = Opsem
end)

module Converter =
  Converter
    (struct
      module Global = Global
    end)
    (struct
      module IntSyn' = IntSyn
    end)
    (struct
      module Abstract = Abstract
    end)
    (struct
      module Tomega' = Tomega
    end)
    (struct
      module Names = Names
    end)
    (struct
      module ModeTable = ModeTable
    end)
    (struct
      module TypeCheck = TypeCheck
    end)
    (struct
      module TomegaAbstract = TomegaAbstract
    end)
    (struct
      module TomegaTypeCheck = TomegaTypeCheck
    end)
    (struct
      module Trail = Trail
    end)
    (struct
      module Unify = UnifyTrail
    end)
    (struct
      module TomegaPrint = TomegaPrint
    end)
    (struct
      module Whnf = Whnf
    end)
    (struct
      module WorldSyn = WorldSyn
    end)
    (struct
      module Worldify = Worldify
    end)
    (struct
      module Subordinate = Subordinate
    end)
    (struct
      module Print = Print
    end)
    (struct
      module Redundant = Redundant
    end)
    (struct
      module Weaken = Weaken
    end)

module TomegaCoverage =
  TomegaCoverage
    (struct
      module Global = Global
    end)
    (struct
      module IntSyn' = IntSyn
    end)
    (struct
      module Tomega' = Tomega
    end)
    (struct
      module TomegaPrint = TomegaPrint
    end)
    (struct
      module TomegaTypeCheck = TomegaTypeCheck
    end)
    (struct
      module Cover = Cover
    end)
