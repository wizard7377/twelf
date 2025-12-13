(* Hash Table *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)

functor (* GEN BEGIN FUNCTOR DECL *) HashTable
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
  	(* GEN BEGIN TAG OUTSIDE LET *) val hashVal = hash key (* GEN END TAG OUTSIDE LET *)
  	(* GEN BEGIN TAG OUTSIDE LET *) val index = hashVal mod n (* GEN END TAG OUTSIDE LET *)
  	(* GEN BEGIN TAG OUTSIDE LET *) val bucket = Array.sub (a, index) (* GEN END TAG OUTSIDE LET *)
  	fun insertB (Cons(r' as ref(hash', e' as (key', datum')), br')) =
  	    if hashVal = hash' andalso eq (key, key')
  	       then (r' := (hashVal, e); SOME (e'))
  	    else insertBR (br')
  	and (* GEN BEGIN FUN FIRST *) insertBR (br as ref(Nil)) =
  	      (br := Cons (ref (hashVal, e), ref Nil); NONE) (* GEN END FUN FIRST *)
  	  | (* GEN BEGIN FUN BRANCH *) insertBR (br) = insertB (!br) (* GEN END FUN BRANCH *)
  	fun (* GEN BEGIN FUN FIRST *) insertA (Nil) =
  	    (Array.update (a, index, Cons (ref (hashVal,e), ref Nil));
  	     NONE) (* GEN END FUN FIRST *)
  	  | (* GEN BEGIN FUN BRANCH *) insertA (bucket) = insertB (bucket) (* GEN END FUN BRANCH *)
      in
  	insertA bucket
      end

  fun insert h e = (insertShadow h e; ())

  fun lookup (a,n) key =
      let
  	(* GEN BEGIN TAG OUTSIDE LET *) val hashVal = hash key (* GEN END TAG OUTSIDE LET *)
  	fun (* GEN BEGIN FUN FIRST *) lookup' (Cons(ref(hash1, (key1, datum1)), br)) =
  	    if hashVal = hash1 andalso eq (key, key1)
  	      then SOME(datum1)
  	    else lookup' (!br) (* GEN END FUN FIRST *)
  	  | (* GEN BEGIN FUN BRANCH *) lookup' (Nil) = NONE (* GEN END FUN BRANCH *)
  	(* GEN BEGIN TAG OUTSIDE LET *) val bucket = Array.sub (a, hashVal mod n) (* GEN END TAG OUTSIDE LET *)
      in
  	lookup' bucket
      end

  fun delete (a,n) key =
      let
  	(* GEN BEGIN TAG OUTSIDE LET *) val hashVal = hash key (* GEN END TAG OUTSIDE LET *)
  	(* GEN BEGIN TAG OUTSIDE LET *) val index = hashVal mod n (* GEN END TAG OUTSIDE LET *)
  	(* GEN BEGIN TAG OUTSIDE LET *) val bucket = Array.sub (a, index) (* GEN END TAG OUTSIDE LET *)
  	fun (* GEN BEGIN FUN FIRST *) deleteBR (br as ref(Cons (ref (hash1, (key1, _)), br1))) =
  	      if hashVal = hash1 andalso eq (key, key1)
                then br := !br1
              else deleteBR br1 (* GEN END FUN FIRST *)
  	  | (* GEN BEGIN FUN BRANCH *) deleteBR (br) = () (* GEN END FUN BRANCH *)
  	fun (* GEN BEGIN FUN FIRST *) deleteA (Nil) = () (* GEN END FUN FIRST *)
          | (* GEN BEGIN FUN BRANCH *) deleteA (Cons (ref (hash1, (key1, _)), br1)) =
            	      if hashVal = hash1 andalso eq (key, key1)
              then
                Array.update (a, index, !br1)
              else deleteBR br1 (* GEN END FUN BRANCH *)
      in
  	deleteA bucket
      end

  fun clear (a,n) = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Nil (* GEN END FUNCTION EXPRESSION *)) a

  fun (* GEN BEGIN FUN FIRST *) appBucket f (Nil) = () (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) appBucket f (Cons(ref(_, e), br)) =
        (f e; appBucket f (!br)) (* GEN END FUN BRANCH *)

  fun app f (a,n) = Array.app (appBucket f) a
end (* GEN END FUNCTOR DECL *);  (* functor HashTable *)
