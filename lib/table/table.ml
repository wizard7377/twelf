open Basis

(* Hash Tables *)

(* Author: Frank Pfenning *)

(* Modified: Roberto Virga *)

(* This provides a common interface to hash tables *)

(* red/black trees and similar data structures *)
open Table_sig


module HashInt : (Hash.HASHABLE with type t = int) = struct 
  type t = int 
  let hash (x : int) : int = x mod 1048576
  let eq (x, y) = x = y
end
(* signature TABLE *)
module StringHashTable = Hash.HashTable
module IntHashTable = Hash.HashTable (HashInt)
module StringRedBlackTree = RedBlackTree.RedBlackTree
module IntRedBlackTree = RedBlackTree.RedBlackTree
module SparseArray = SparseArray.SparseArray (IntHashTable)
module SparseArray2 = SparseArray2.SparseArray2 (IntHashTable)
