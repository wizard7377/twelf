module MetaSyn = 
  MetaSyn ((*! module IntSyn' = IntSyn !*)
	   module Whnf = Whnf);

module MetaAbstract = 
  MetaAbstract (module Global = Global
                module MetaSyn' = MetaSyn
		module MetaGlobal = MetaGlobal
		module Abstract = Abstract
		module ModeTable = ModeTable
		module Whnf = Whnf
		module Print = Print
		module Constraints = Constraints
		module Unify = UnifyNoTrail
		module Names = Names
		module TypeCheck = TypeCheck
		module Subordinate = Subordinate
                (*! module CSManager = CSManager !*)
		  );

module MetaPrint = 
  MetaPrint (module Global = Global
	     module MetaSyn' = MetaSyn
	     module Formatter = Formatter
	     module Print = Print
	     module ClausePrint = ClausePrint);

module Init = 
  Init (module MetaSyn' = MetaSyn
	module MetaAbstract = MetaAbstract);

module OLDSearch = 
  OLDSearch (module MetaGlobal = MetaGlobal
	  module Conv = Conv
	  module MetaSyn' = MetaSyn
	  (*! module CompSyn' = CompSyn !*)
	  module Compile = Compile
	  module Whnf = Whnf
	  module Unify = UnifyTrail
	  module Index = IndexSkolem
	  (* module Assign = Assign *)
	  module CPrint = CPrint
	  module Print = Print
	  module Names = Names
          (*! module CSManager = CSManager !*)
	    );

module Lemma =
  Lemma (module MetaSyn' = MetaSyn
	 module MetaAbstract = MetaAbstract);

module Splitting =
  Splitting (module Global = Global
	     module MetaSyn' = MetaSyn
	     module MetaPrint = MetaPrint
	     module MetaAbstract = MetaAbstract
	     module Whnf = Whnf
	     module ModeTable = ModeTable
	     module Index = Index
	     module Print = Print
	     module Unify = UnifyTrail
             (*! module CSManager = CSManager !*)
	       );

module Filling =
  Filling (module Global = Global
	   module MetaSyn' = MetaSyn
	   module MetaAbstract = MetaAbstract
	   module Print = Print
	   module Search = OLDSearch
	   module Whnf = Whnf);

module Recursion =
  Recursion (module Global = Global
	     module MetaSyn' = MetaSyn
	     module MetaPrint = MetaPrint
	     module Whnf = Whnf
	     module Unify = UnifyTrail
	     module Conv = Conv
	     module Names = Names
	     module Print = Print
	     module Subordinate = Subordinate
	     module Order = Order
	     module ModeTable = ModeTable
	     module MetaAbstract = MetaAbstract
	     module Lemma = Lemma
	     module Filling = Filling
	     module Formatter = Formatter
             (*! module CSManager = CSManager !*)
	       );

module Qed = 
  Qed (module Global = Global
       module MetaSyn' = MetaSyn);

module StrategyFRS = 
  StrategyFRS (module MetaGlobal = MetaGlobal
	       module MetaSyn' = MetaSyn
	       module MetaAbstract = MetaAbstract 
	       module Lemma = Lemma
	       module Filling = Filling
	       module Recursion = Recursion
	       module Splitting = Splitting
	       module Qed = Qed
	       module MetaPrint = MetaPrint
	       module Timers = Timers);

module StrategyRFS = 
  StrategyRFS (module MetaGlobal = MetaGlobal
	       module MetaSyn' = MetaSyn
	       module MetaAbstract = MetaAbstract 
	       module Lemma = Lemma
	       module Filling = Filling
	       module Recursion = Recursion
	       module Splitting = Splitting
	       module Qed = Qed
	       module MetaPrint = MetaPrint
	       module Timers = Timers);

module Strategy = 
  Strategy (module MetaGlobal = MetaGlobal
	    module MetaSyn' = MetaSyn
	    module StrategyFRS = StrategyFRS
	    module StrategyRFS = StrategyRFS);

module Prover = 
  Prover (module MetaGlobal = MetaGlobal
	  module MetaSyn' = MetaSyn
	  module MetaAbstract = MetaAbstract 
	  module MetaPrint = MetaPrint
	  module Filling = Filling
	  module Splitting = Splitting
	  module Recursion = Recursion
	  module Init = Init
	  module Strategy = Strategy
	  module Qed = Qed
	  module Names = Names
	  module Timers = Timers);

module Mpi = 
  Mpi (module MetaGlobal = MetaGlobal
       module MetaSyn' = MetaSyn
       module MetaAbstract = MetaAbstract 
       module Init = Init
       module Lemma = Lemma
       module Filling = Filling
       module Recursion = Recursion
       module Splitting = Splitting
       module Strategy = Strategy
       module Qed = Qed
       module MetaPrint = MetaPrint
       module Names = Names
       module Timers = Timers
       module Ring = Ring);

module Skolem = 
  Skolem (module Global = Global
          (*! module IntSyn' = IntSyn !*)
	  module Whnf = Whnf
	  module Abstract = Abstract
	  module IndexSkolem = IndexSkolem
	  module ModeTable = ModeTable
	  module Print = Print
	  module Timers = Timers
	  module Compile = Compile
	  module Names = Names);