structure MemoTable =
  HashTable (type key' = int * int
	     (* GEN BEGIN TAG INSIDE LET *) val hash = (fn (n,m) => 7 * n + m) (* GEN END TAG INSIDE LET *)
             (* GEN BEGIN TAG INSIDE LET *) val eq = (op =) (* GEN END TAG INSIDE LET *));

structure Subordinate = 
  Subordinate (structure Global = Global
	       (*! structure IntSyn' = IntSyn !*)
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Table = IntRedBlackTree
	       structure MemoTable = MemoTable
	       structure IntSet = IntSet);
