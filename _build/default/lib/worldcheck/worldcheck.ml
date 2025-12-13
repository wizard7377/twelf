structure MemoTable =
  HashTable (type key' = int * int
	     (* GEN BEGIN TAG OUTSIDE LET *) val hash = ((* GEN BEGIN FUNCTION EXPRESSION *) fn (n,m) => 7 * n + m (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val eq = (op =) (* GEN END TAG OUTSIDE LET *));

structure WorldSyn = 
  WorldSyn (structure Global = Global
	    structure Whnf = Whnf
	    structure Names = Names
	    structure Unify = UnifyTrail
	    structure Abstract = Abstract
	    structure Constraints = Constraints
	    structure Index = Index
	    (*! structure CSManager = CSManager !*)
	    structure Subordinate = Subordinate
	    structure Print = Print
	    structure Table = IntRedBlackTree
	    structure Paths = Paths
	    structure Origins = Origins
            structure Timers = Timers);

structure Worldify = Worldify 
  (structure Global = Global
   (*! structure IntSyn = IntSyn !*)
   structure WorldSyn = WorldSyn
   (*! structure Tomega = Tomega !*)
   structure Whnf = Whnf
   structure Names = Names
   structure Unify = UnifyTrail
   structure Abstract = Abstract
   structure Constraints = Constraints
   structure Index = Index
   structure CSManager = CSManager
   structure Subordinate = Subordinate
   structure Print = Print
   structure Table = IntRedBlackTree
   structure MemoTable = MemoTable
   structure IntSet = IntSet 
  (*! structure Paths = Paths !*)
   structure Origins = Origins);


