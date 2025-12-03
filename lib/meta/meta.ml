module MTPGlobal = 
  MTPGlobal (module MetaGlobal = MetaGlobal)

(* Now in funsyn.fun *)
(*
module FunSyn = 
  FunSyn ((*! module IntSyn' = IntSyn !*)
	  module Whnf = Whnf
	  module Conv = Conv);
*)

module StateSyn = 
  StateSyn ((*! module FunSyn' = FunSyn !*)
	    (*! module IntSyn' = IntSyn !*)
	    module Whnf = Whnf
	    module Conv = Conv)

module FunNames = 
  FunNames (module Global = Global
	    (*! module FunSyn' = FunSyn !*)
	    module HashTable = StringHashTable);

module FunPrint = 
  FunPrint ((*! module FunSyn' = FunSyn !*)
	    module Formatter = Formatter
	    module Print = Print
	    module Names = Names);
(* moves eventually into the Twelf core *)
module Weaken =
  Weaken ((*! module IntSyn' = IntSyn !*)
	  module Whnf = Whnf)

module FunWeaken =
  FunWeaken ((*! module FunSyn' = FunSyn !*)
	     module Weaken = Weaken)

module FunTypeCheck = 
  FunTypeCheck ((*! module FunSyn' = FunSyn !*)
		module StateSyn' = StateSyn
	        module Abstract = Abstract
	        module TypeCheck = TypeCheck
	        module Conv = Conv
		module Weaken = Weaken
		module Subordinate = Subordinate
		module Whnf = Whnf
		module Print = Print
		module FunPrint = FunPrint);

module RelFun = 
  RelFun (module Global = Global
          (*! module FunSyn' = FunSyn !*)
	  module ModeTable = ModeTable
	  module Names = Names
	  module TypeCheck = TypeCheck
	  module Trail = Trail
	  module Unify = UnifyTrail
	  module Whnf = Whnf
	  module Print = Print
	  module Weaken = Weaken
	  module FunWeaken = FunWeaken
	  module FunNames = FunNames);

(* Functor instantiation for the Prover *)

module MTPData = 
  MTPData (module MTPGlobal = MTPGlobal)

module MTPAbstract =
  MTPAbstract ((*! module IntSyn' = IntSyn !*)
               (*! module FunSyn' = FunSyn !*)
	       module StateSyn' = StateSyn
	       module Whnf = Whnf
	       module Constraints = Constraints
               module Unify = UnifyTrail
	       module Subordinate = Subordinate
	       module TypeCheck = TypeCheck
	       module FunTypeCheck = FunTypeCheck
	       module Abstract = Abstract);


module MTPInit = 
  MTPInit (module MTPGlobal = MTPGlobal
	   (*! module IntSyn = IntSyn !*)
	   module Names = Names
	   (*! module FunSyn' = FunSyn !*)
	   module StateSyn' = StateSyn
	   module MTPData = MTPData
	   module Formatter = Formatter
	   module Whnf = Whnf
	   module Print = Print
	   module FunPrint = FunPrint)

module MTPrint = 
  MTPrint (module Global = Global
	   (*! module IntSyn = IntSyn !*)
	   (*! module FunSyn = FunSyn !*)
	   module Names = Names
	   module StateSyn' = StateSyn
	   module Formatter' = Formatter
	   module Print = Print
	   module FunPrint = FunPrint)



module MTPSearch = 
  MTPSearch (module Global = Global
             module MTPGlobal = MTPGlobal
	     (*! module IntSyn' = IntSyn !*)
	     module Abstract = Abstract
	     module Conv = Conv
	     module StateSyn' = StateSyn
	     (*! module CompSyn' = CompSyn !*)
	     module Compile = Compile
	     module Whnf = Whnf
	     module Unify = UnifyTrail
	     module Index = IndexSkolem
	     module Assign = Assign 
	     module CPrint = CPrint
	     module Print = Print
	     module Names = Names
             (*! module CSManager = CSManager  !*)
	       );

module MTPFilling =
  MTPFilling (module MTPGlobal = MTPGlobal
              (*! module IntSyn = IntSyn !*)
	      (*! module FunSyn' = FunSyn !*)
	      module StateSyn' = StateSyn
	      module MTPData = MTPData
	      module Whnf = Whnf
	      module Abstract = Abstract
	      module TypeCheck = TypeCheck
	      module Search = MTPSearch
	      module Whnf = Whnf)

module MTPSplitting = 
  MTPSplitting (module MTPGlobal = MTPGlobal
		module Global = Global
		(*! module IntSyn = IntSyn !*)
		(*! module FunSyn = FunSyn !*)
		module StateSyn' = StateSyn
		module Heuristic = Heuristic
		module MTPrint = MTPrint
		module MTPAbstract = MTPAbstract
		module Names = Names  (* to be removed -cs *)
		module Conv = Conv
		module Whnf = Whnf
		module TypeCheck = TypeCheck
		module Subordinate = Subordinate
		module FunTypeCheck = FunTypeCheck
		module Index = Index
		module Print = Print
		module Unify = UnifyTrail
                (*! module CSManager = CSManager !*)
		  ); 

module UniqueSearch =
  UniqueSearch (module Global = Global
		(*! module IntSyn' = IntSyn !*)
		(*! module FunSyn' = FunSyn !*)
		module StateSyn' = StateSyn
		module Abstract = Abstract
		module MTPGlobal = MTPGlobal
		(*! module CompSyn' = CompSyn !*)
		module Whnf = Whnf
		module Unify = UnifyTrail
		module Assign = Assign		
		module Index = Index
		module Compile = Compile
		module CPrint = CPrint
		module Print = Print
		module Names = Names
                (*! module CSManager = CSManager !*)
		  ); 

module Inference = 
  Inference (module MTPGlobal = MTPGlobal
	     (*! module IntSyn = IntSyn !*)
	     (*! module FunSyn' = FunSyn !*)
	     module StateSyn' = StateSyn
	     module Abstract = Abstract
	     module TypeCheck = TypeCheck
	     module FunTypeCheck = FunTypeCheck
	     module UniqueSearch = UniqueSearch
	     module Whnf = Whnf
	     module Print = Print)

		  
module MTPRecursion = 
  MTPRecursion (module MTPGlobal = MTPGlobal
                module Global =  Global
		(*! module IntSyn = IntSyn !*)
		(*! module FunSyn = FunSyn !*)
		module StateSyn' = StateSyn
		module FunTypeCheck = FunTypeCheck
		module MTPSearch = MTPSearch
		module Abstract = Abstract
		module MTPAbstract = MTPAbstract
		module Whnf = Whnf
		module Unify = UnifyTrail
		module Conv = Conv
		module Names = Names
		module Subordinate = Subordinate
		module MTPrint = MTPrint
		module Print = Print
		module TypeCheck = TypeCheck
		module FunPrint = FunPrint
		module Formatter = Formatter
                (*! module CSManager = CSManager !*)
		  ); 



module MTPStrategy = 
  MTPStrategy (module MTPGlobal = MTPGlobal
	       module StateSyn' = StateSyn
	       module MTPrint = MTPrint
	       module MTPData = MTPData
	       module MTPFilling = MTPFilling
	       module MTPSplitting = MTPSplitting
	       module MTPRecursion = MTPRecursion
	       module Inference = Inference
	       module Timers = Timers)

module MTProver =
  MTProver (module MTPGlobal = MTPGlobal
            (*! module IntSyn' = IntSyn !*)
            (*! module FunSyn = FunSyn !*)
	    module StateSyn = StateSyn
	    module Order = Order
	    module MTPrint = MTPrint
	    module MTPInit = MTPInit
	    module MTPStrategy = MTPStrategy
	    module RelFun = RelFun)

module CombiProver = 
  CombiProver (module MTPGlobal = MTPGlobal
	       (*! module IntSyn' = IntSyn !*)
	       module ProverNew = MTProver
	       module ProverOld = Prover)


module MTPi = 
  MTPi (module MTPGlobal = MTPGlobal
	(*! module IntSyn = IntSyn !*)
	(*! module FunSyn' = FunSyn !*)
	module StateSyn' = StateSyn
	module FunTypeCheck = FunTypeCheck
	module RelFun = RelFun
	module Formatter = Formatter
	module Print = Print
	module MTPrint = MTPrint
	module MTPInit = MTPInit
	module MTPFilling = MTPFilling
	module MTPData = MTPData
	module MTPSplitting = MTPSplitting
	module MTPRecursion = MTPRecursion
	module Inference = Inference
	module MTPStrategy = MTPStrategy
	module Names = Names
	module Order = Order
	module Timers = Timers
	module Ring = Ring)
	  