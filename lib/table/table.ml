module StringHashTable = HashTable
module IntHashTable = HashTable
module StringRedBlackTree = RedBlackTree
module IntRedBlackTree = RedBlackTree

module SparseArray = SparseArray (struct
  module IntTable = IntHashTable
end)

module SparseArray2 = SparseArray2 (struct
  module IntTable = IntHashTable
end)
