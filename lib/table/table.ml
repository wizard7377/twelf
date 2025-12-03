module StringHashTable =
  HashTable (type key' = string
             let hash = StringHash.stringHash
             let eq = (op =));

module IntHashTable =
  HashTable (type key' = int
             let hash = (fun n -> n)
             let eq = (op =));

module StringRedBlackTree =
  RedBlackTree (type key' = string
		let compare = String.compare) 

module IntRedBlackTree =
  RedBlackTree (type key' = int
		let compare = Int.compare) 

module SparseArray =
  SparseArray(module IntTable = IntHashTable)

module SparseArray2 =
  SparseArray2(module IntTable = IntHashTable)


