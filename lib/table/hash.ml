(* Hash Tables *)
(* Author: Frank Pfenning *)

module HashTable
  (type key'
   let hash : key' -> int
   let eq : key' * key' -> bool)
  :> TABLE where type key = key' =
struct
  type key = key'
  type 'a entry = key * 'a

  (* A hashtable bucket is a linked list of mutable elements *)
  (* A hashtable is an array of buckets containing entries paired with hash values *)
  type 'a bucket = Nil | Cons of 'a ref * ('a bucket) ref
  type 'a Table = ((int * 'a entry) bucket) array * int

  fun new (n) = (Array.array (n,Nil), n)

  fun insertShadow (a,n) (e as (key, datum)) =
      let
	let hashVal = hash key
	let index = hashVal mod n
	let bucket = Array.sub (a, index)
	fun insertB (Cons(r' as ref(hash', e' as (key', datum')), br')) =
	    if hashVal = hash' andalso eq (key, key')
	       then (r' := (hashVal, e); SOME (e'))
	    else insertBR (br')
	and insertBR (br as ref(Nil)) =
	      (br := Cons (ref (hashVal, e), ref Nil); NONE)
	  | insertBR (br) = insertB (!br)
	fun insertA (Nil) =
	    (Array.update (a, index, Cons (ref (hashVal,e), ref Nil));
	     NONE)
	  | insertA (bucket) = insertB (bucket)
      in
	insertA bucket
      end

  fun insert h e = (insertShadow h e; ())

  fun lookup (a,n) key =
      let
	let hashVal = hash key
	fun lookup' (Cons(ref(hash1, (key1, datum1)), br)) =
	    if hashVal = hash1 andalso eq (key, key1)
	      then SOME(datum1)
	    else lookup' (!br)
	  | lookup' (Nil) = NONE
	let bucket = Array.sub (a, hashVal mod n)
      in
	lookup' bucket
      end

  fun clear (a,n) = Array.modify (fun _ -> Nil) a

  fun appBucket f (Nil) = ()
    | appBucket f (Cons(ref(_, e), br)) =
        (f e; appBucket f (!br))

  fun app f (a,n) = Array.app (appBucket f) a
end;; (* functor HashTable *)

module type STRING_HASH =
sig
  let stringHash : string -> int
end;

module StringHash : STRING_HASH =
struct
  fun stringHash (s) =
      (* sample 4 characters from string *)
      let
	fun num (i) = Char.ord (String.sub (s,i)) mod 128
	let n = String.size (s)
      in
	if n = 0 then 0
	else let
	       let a = n-1
	       let b = n div 2
	       let c = b div 2
	       let d = b + c
	     in
	       num(a)+128*(num(b)+128*(num(c)+128*num(d)))
	     end
      end
end;; (* module StringHash *)

module StringHashTable
  :> TABLE where type key = string =
  HashTable (type key' = string
	     let hash = StringHash.stringHash
	     let eq = (op =));
