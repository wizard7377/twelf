(* Hash Table *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)

functor HashTable
  (type key'
   val hash : key' -> int
   val eq : key' * key' -> bool)
  :> TABLE where type key = key' =
struct
  type key = key'
  type 'a entry = key * 'a

  (* A hashtable bucket is a linked list of mutable elements *)
  (* A hashtable is an array of buckets containing entries paired with hash values *)
  datatype 'a bucket = Nil | Cons of 'a ref * ('a bucket) ref
  type 'a table = ((int * 'a entry) bucket) array * int

  fun new (n) = (Array.array (n,Nil), n)

  fun insertShadow (a,n) (e as (key, datum)) =
      let
  	val hashVal = hash key
  	val index = hashVal mod n
  	val bucket = Array.sub (a, index)
  	fun insertB (Cons(r' as ref(hash', e' as (key', datum')), br')) =
  	    if hashVal = hash' andalso eq (key, key')
  	       then (r' := (hashVal, e); SOME (e'))
  	    else insertBR (br')
  	and insertBR (br as ref(Nil)) =
  	      (br := Cons (ref (hashVal, e), ref Nil); NONE)
  	  | (* GEN CASE BRANCH *) insertBR (br) = insertB (!br)
  	fun insertA (Nil) =
  	    (Array.update (a, index, Cons (ref (hashVal,e), ref Nil));
  	     NONE)
  	  | (* GEN CASE BRANCH *) insertA (bucket) = insertB (bucket)
      in
  	insertA bucket
      end

  fun insert h e = (insertShadow h e; ())

  fun lookup (a,n) key =
      let
  	val hashVal = hash key
  	fun lookup' (Cons(ref(hash1, (key1, datum1)), br)) =
  	    if hashVal = hash1 andalso eq (key, key1)
  	      then SOME(datum1)
  	    else lookup' (!br)
  	  | (* GEN CASE BRANCH *) lookup' (Nil) = NONE
  	val bucket = Array.sub (a, hashVal mod n)
      in
  	lookup' bucket
      end

  fun delete (a,n) key =
      let
  	val hashVal = hash key
  	val index = hashVal mod n
  	val bucket = Array.sub (a, index)
  	fun deleteBR (br as ref(Cons (ref (hash1, (key1, _)), br1))) =
  	      if hashVal = hash1 andalso eq (key, key1)
                then br := !br1
              else deleteBR br1
  	  | (* GEN CASE BRANCH *) deleteBR (br) = ()
  	fun deleteA (Nil) = ()
          | (* GEN CASE BRANCH *) deleteA (Cons (ref (hash1, (key1, _)), br1)) =
            	      if hashVal = hash1 andalso eq (key, key1)
              then
                Array.update (a, index, !br1)
              else deleteBR br1
      in
  	deleteA bucket
      end

  fun clear (a,n) = Array.modify (fn _ => Nil) a

  fun appBucket f (Nil) = ()
    | (* GEN CASE BRANCH *) appBucket f (Cons(ref(_, e), br)) =
        (f e; appBucket f (!br))

  fun app f (a,n) = Array.app (appBucket f) a
end;  (* functor HashTable *)
