structure StringHashTable =
  HashTable (type key' = string
             (* GEN BEGIN TAG OUTSIDE LET *) val hash = StringHash.stringHash (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val eq = (op =) (* GEN END TAG OUTSIDE LET *));

structure IntHashTable =
  HashTable (type key' = int
             (* GEN BEGIN TAG OUTSIDE LET *) val hash = ((* GEN BEGIN FUNCTION EXPRESSION *) fn n => n (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
             (* GEN BEGIN TAG OUTSIDE LET *) val eq = (op =) (* GEN END TAG OUTSIDE LET *));

structure StringRedBlackTree =
  RedBlackTree (type key' = string
		(* GEN BEGIN TAG OUTSIDE LET *) val compare = String.compare (* GEN END TAG OUTSIDE LET *)) 

structure IntRedBlackTree =
  RedBlackTree (type key' = int
		(* GEN BEGIN TAG OUTSIDE LET *) val compare = Int.compare (* GEN END TAG OUTSIDE LET *)) 

structure SparseArray =
  SparseArray(structure IntTable = IntHashTable)

structure SparseArray2 =
  SparseArray2(structure IntTable = IntHashTable)


