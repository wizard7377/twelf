structure StringHashTable =
  HashTable (type key' = string
             (* GEN BEGIN TAG INSIDE LET *) val hash = StringHash.stringHash (* GEN END TAG INSIDE LET *)
             (* GEN BEGIN TAG INSIDE LET *) val eq = (op =) (* GEN END TAG INSIDE LET *));

structure IntHashTable =
  HashTable (type key' = int
             (* GEN BEGIN TAG INSIDE LET *) val hash = (fn n => n) (* GEN END TAG INSIDE LET *)
             (* GEN BEGIN TAG INSIDE LET *) val eq = (op =) (* GEN END TAG INSIDE LET *));

structure StringRedBlackTree =
  RedBlackTree (type key' = string
		(* GEN BEGIN TAG INSIDE LET *) val compare = String.compare (* GEN END TAG INSIDE LET *)) 

structure IntRedBlackTree =
  RedBlackTree (type key' = int
		(* GEN BEGIN TAG INSIDE LET *) val compare = Int.compare (* GEN END TAG INSIDE LET *)) 

structure SparseArray =
  SparseArray(structure IntTable = IntHashTable)

structure SparseArray2 =
  SparseArray2(structure IntTable = IntHashTable)


