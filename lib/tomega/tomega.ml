module TomegaAbstract = TomegaAbstract 
  (module Global = Global
   module Abstract = Abstract
   module Whnf = Whnf
   module Subordinate = Subordinate);
  

module TomegaPrint = TomegaPrint
  ((*! module IntSyn' = IntSyn !*)
   (*! module Tomega' = Tomega !*)
   module Formatter = Formatter
   module Names = Names
   module Print = Print)

module TomegaTypeCheck = TomegaTypeCheck
  (module Global = Global
   (*! module IntSyn' = IntSyn !*)
   module Abstract = Abstract
   (*! module Tomega' = Tomega !*)
   module TypeCheck = TypeCheck
   module Conv = Conv
   module Whnf = Whnf
   module Subordinate = Subordinate
   module TomegaPrint = TomegaPrint
   module Print = Print
   module Weaken = Weaken
   module TomegaAbstract = TomegaAbstract);

(* module TomegaUnify = TomegaUnify
  (module Global = Global
   (*! module IntSyn' = IntSyn !*)
   module Abstract = Abstract
   (*! module Tomega' = Tomega !*)
   module TypeCheck = TypeCheck
   module Normalize = Normalize
   module Conv = Conv
   module Whnf = Whnf
   module Subordinate = Subordinate
   module TomegaPrint = TomegaPrint
   module Print = Print
   module Weaken = Weaken);
*)


module Opsem = Opsem
  (module Global = Global
   module IntSyn' = IntSyn
   module Abstract = Abstract
   module Tomega' = Tomega
   module TypeCheck = TypeCheck
   module Unify = UnifyNoTrail
   module Conv = Conv
   module Whnf = Whnf
   module Print = Print
   module Subordinate = Subordinate
   module TomegaPrint = TomegaPrint
   module TomegaTypeCheck = TomegaTypeCheck
   module Weaken = Weaken);

(*
module Opsem = OpsemCont
  (module Global = Global
   module IntSyn' = IntSyn
   module Abstract = Abstract
   module Tomega' = Tomega
   module TypeCheck = TypeCheck
   module Normalize = Normalize
   module Unify = UnifyNoTrail
   module Conv = Conv
   module Whnf = Whnf
   module Print = Print
   module Subordinate = Subordinate
   module TomegaPrint = TomegaPrint
   module TomegaTypeCheck = TomegaTypeCheck
   module Weaken = Weaken);
*)

module Redundant = Redundant
  (module Opsem = Opsem)


module Converter = Converter
  (module Global = Global
   module IntSyn' = IntSyn
   module Abstract = Abstract
   module Tomega' = Tomega
   module Names = Names
   module ModeTable = ModeTable
   module TypeCheck = TypeCheck
   module TomegaAbstract = TomegaAbstract
   module TomegaTypeCheck = TomegaTypeCheck
   module Trail = Trail
   module Unify = UnifyTrail
   module TomegaPrint = TomegaPrint
   module Whnf = Whnf
   module WorldSyn = WorldSyn
   module Worldify = Worldify
   module Subordinate = Subordinate
   module Print = Print
   module Redundant = Redundant
   module Weaken = Weaken);


module TomegaCoverage = TomegaCoverage
  (module Global = Global
   module IntSyn' = IntSyn
   module Tomega' = Tomega
   module TomegaPrint = TomegaPrint
   module TomegaTypeCheck = TomegaTypeCheck
   module Cover = Cover);
