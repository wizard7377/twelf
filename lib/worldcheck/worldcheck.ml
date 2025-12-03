module MemoTable =
  HashTable (type key' = int * int
	     let hash = (fn (n,m) => 7 * n + m)
             let eq = (op =));

module WorldSyn = 
  WorldSyn (module Global = Global
	    module Whnf = Whnf
	    module Names = Names
	    module Unify = UnifyTrail
	    module Abstract = Abstract
	    module Constraints = Constraints
	    module Index = Index
	    (*! module CSManager = CSManager !*)
	    module Subordinate = Subordinate
	    module Print = Print
	    module Table = IntRedBlackTree
	    module Paths = Paths
	    module Origins = Origins
            module Timers = Timers);

module Worldify = Worldify 
  (module Global = Global
   (*! module IntSyn = IntSyn !*)
   module WorldSyn = WorldSyn
   (*! module Tomega = Tomega !*)
   module Whnf = Whnf
   module Names = Names
   module Unify = UnifyTrail
   module Abstract = Abstract
   module Constraints = Constraints
   module Index = Index
   module CSManager = CSManager
   module Subordinate = Subordinate
   module Print = Print
   module Table = IntRedBlackTree
   module MemoTable = MemoTable
   module IntSet = IntSet 
  (*! module Paths = Paths !*)
   module Origins = Origins);


