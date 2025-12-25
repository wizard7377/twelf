open Basis ;; 
(* Hash Tables *)

(* Author: Frank Pfenning *)

(* Modified: Roberto Virga *)

(* This provides a common interface to hash tables *)

(* red/black trees and similar data structures *)

module type TABLE = sig
  type key

  (* parameter *)
  type 'a entry = key * 'a
  type 'a table

  val new_ : int -> 'a table

  (* size hint for_sml some implementations *)
  val insert : 'a table -> 'a entry -> unit

  (* insert entry, return shadowed entry if there is one *)
  val insertShadow : 'a table -> 'a entry -> 'a entry option
  val lookup : 'a table -> key -> 'a option
  val delete : 'a table -> key -> unit
  val clear : 'a table -> unit

  (* Apply function to all entries in unpredictable order *)
  val app : ('a entry -> unit) -> 'a table -> unit
end

(* signature TABLE *)
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
