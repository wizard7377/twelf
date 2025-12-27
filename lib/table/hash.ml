open Basis
open Common
(* Hash Tables *)

(* Author: Frank Pfenning *)

module type HASHABLE = sig
  type t

  val hash : t -> int
  val eq : t * t -> bool
end

module HashTable (Hash : HASHABLE) : Table_sig.TABLE with type key = Hash.t =
struct
  type key = Hash.t
  type 'a entry = key * 'a
  (* A hashtable bucket is a linked list of mutable elements *)

  (* A hashtable is an array of buckets containing entries paired with hash values *)

  type 'a bucket = Nil | Cons of 'a ref * 'a bucket ref
  type 'a table = 'a entry bucket array * int
  let rec insertShadow = todo_hole
  let rec insert = todo_hole
  let rec lookup = todo_hole
  let rec clear = todo_hole
  let rec delete = todo_hole
  let rec app = todo_hole
  let rec new_ n = todo_hole

(* TODO
  let rec new_ n = (Array.array (n, Nil), n)

  let rec insertShadow (a, n) e =
    let key, _ = e in
    let hashVal = Hash.hash key in
    let index = hashVal mod n in
    let bucket = Array.sub (a, index) in
    let rec insertB (Cons (r', br')) =
      let hash', ((key', _) as e') = !r' in
      if hashVal = hash' && Hash.eq (key, key') then (
        r' := (hashVal, e);
        Some e')
      else insertBR br'
    and insertBR = function
      | br ->
          br := Cons (ref (hashVal, e), ref Nil);
          None
      | br -> insertB !br
    in
    let rec insertA = function
      | Nil ->
          Array.update (a, index, Cons (ref (hashVal, e), ref Nil));
          None
      | bucket -> insertB bucket
    in
    insertA bucket

  let rec insert h e =
    insertShadow h e;
    ()

  let rec lookup (a, n) key =
    let hashVal = Hash.hash key in
    let rec lookup' = function
      | Cons ({ contents = hash1, (key1, datum1) }, br) ->
          if hashVal = hash1 && Hash.eq (key, key1) then Some datum1
          else lookup' !br
      | Nil -> None
    in
    let bucket = Array.sub (a, hashVal mod n) in
    lookup' bucket

  let rec clear (a, n) = Array.modify (fun _ -> Nil) a

  let rec delete (a, n) key =
    let hashVal = Hash.hash key in
    let index = hashVal mod n in
    let bucket = Array.sub (a, index) in
    let rec deleteBR br =
      match !br with
      | Nil -> ()
      | Cons ({ contents = hash1, (key1, _) }, br1) ->
          if hashVal = hash1 && Hash.eq (key, key1) then br := !br1
          else deleteBR br1
    in
    match bucket with
    | Nil -> ()
    | Cons ({ contents = hash1, (key1, _) }, br1) ->
        if hashVal = hash1 && Hash.eq (key, key1) then
          Array.update (a, index, !br1)
        else deleteBR br1

  let rec appBucket f = function
    | Nil -> ()
    | Cons ({ contents = _, e }, br) ->
        f e;
        appBucket f !br

  let rec app f (a, n) = Array.app (appBucket f) a
*)
end

(* functor HashTable *)
