module AbsMachine = 
  AbsMachine ((*! module IntSyn' = IntSyn !*)
              (*! module CompSyn' = CompSyn !*)
              module Unify = UnifyTrail
	      module Assign = Assign 
	      module Index = Index
              module CPrint = CPrint
              module Print = Print
              module Names = Names
              (*! module CSManager = CSManager !*)
		); 

module AbstractTabled =
  AbstractTabled ((*! module IntSyn' = IntSyn !*)
		  module Print = Print
		  module Whnf = Whnf
		  module Unify = UnifyTrail
		  module Constraints = Constraints
		  module Subordinate = Subordinate
		  (*! module TableParam = TableParam !*)
		  module Conv = Conv
		  module Print = Print);

module MemoTable =
 MemoTable ((*! module IntSyn' = IntSyn !*)
	    (*! module CompSyn' = CompSyn !*)
	    module Conv = Conv
	    module Whnf = Whnf
	    module Print = Print
	    (*! module TableParam = TableParam !*)
	    module AbstractTabled = AbstractTabled
	    module Table = IntRedBlackTree
	    (*! module RBSet = RBSet!*))


module MemoTableInst =
 MemoTableInst ((*! module IntSyn' = IntSyn !*)
		(*! module CompSyn' = CompSyn !*)
		module Conv = Conv
		module Whnf = Whnf
		module Match = Match
		module Assign = Assign
		module Print = Print
		(*! module TableParam = TableParam !*)
		module AbstractTabled = AbstractTabled
		module Table = IntRedBlackTree
		(*! module RBSet = RBSet!*))


module SwMemoTable =
 SwMemoTable ((*! module TableParam = TableParam !*)
	      module MemoTable = MemoTable
	      module MemoTableInst = MemoTableInst)

module Tabled = 
  Tabled ((*! module IntSyn' = IntSyn !*)
          (*! module CompSyn' = CompSyn !*)
	  module Unify = UnifyTrail 
	  module Match = Match
	  module TabledSyn = TabledSyn
	  module Assign = Assign 
	  module Index = Index
	  module Queue = Queue
	  (*! module TableParam = TableParam !*)
(*	  module MemoTable = MemoTable    *)
	  module MemoTable = SwMemoTable    
	  module AbstractTabled = AbstractTabled
	  module CPrint = CPrint
	  module Print = Print
(*	  module Names = Names*)
	  (*! module CSManager = CSManager !*)
(*	  module Subordinate = Subordinate*)); 


module PtRecon = 
  PtRecon ((*! module IntSyn' = IntSyn !*)
           (*! module CompSyn' = CompSyn !*)
	  module Unify = UnifyTrail
	  (*! module TableParam = TableParam !*)
	  module MemoTable = SwMemoTable    
	  module Assign = Assign 
	  module Index = Index
	  module CPrint = CPrint
	  module Names = Names
	  (*! module CSManager = CSManager !*)
	    ); 

module Trace =
  Trace ((*! module IntSyn' = IntSyn !*)
	 module Names = Names
	 module Whnf = Whnf
	 module Abstract = Abstract
	 module Print = Print);


module AbsMachineSbt = 
  AbsMachineSbt (module IntSyn' = IntSyn
              module CompSyn' = CompSyn
	      module SubTree = SubTree
              module Unify = UnifyTrail
	      module Assign = Assign 
	      module Index = Index
              module CPrint = CPrint
              module Print = Print
              module Names = Names
              module CSManager = CSManager); 

module TMachine =
  TMachine ((*! module IntSyn' = IntSyn !*)
            (*! module CompSyn' = CompSyn !*)
	    module Unify = UnifyTrail
	    module Index = Index
	    module Assign = Assign 
	    module CPrint = CPrint
            module Names = Names
	    module Trace = Trace
	    (*! module CSManager = CSManager !*)
		);

module SwMachine =
  SwMachine (module Trace = Trace
	     module AbsMachine = AbsMachine
             module TMachine = TMachine);

