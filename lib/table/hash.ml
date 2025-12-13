(* Hash Tables *)
(* Author: Frank Pfenning *)

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

  fun clear (a,n) = Array.modify ((* GEN BEGIN FUNCTION EXPRESSION *) fn _ => Nil (* GEN END FUNCTION EXPRESSION *)) a

  fun (* GEN BEGIN FUN FIRST *) appBucket f (Nil) = () (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) appBucket f (Cons(ref(_, e), br)) =
        (f e; appBucket f (!br)) (* GEN END FUN BRANCH *)

  fun app f (a,n) = Array.app (appBucket f) a
end (* GEN END FUNCTOR DECL *);  (* functor HashTable *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature STRING_HASH =
sig
  val stringHash : string -> int
end (* GEN END SIGNATURE DECLARATION *);

structure StringHash :> STRING_HASH =
struct
  fun stringHash (s) =
      (* sample 4 characters from string *)
      let
  	fun num (i) = Char.ord (String.sub (s,i)) mod 128
  	(* GEN BEGIN TAG OUTSIDE LET *) val n = String.size (s) (* GEN END TAG OUTSIDE LET *)
      in
  	if n = 0 then 0
  	else let
  	       (* GEN BEGIN TAG OUTSIDE LET *) val a = n-1 (* GEN END TAG OUTSIDE LET *)
  	       (* GEN BEGIN TAG OUTSIDE LET *) val b = n div 2 (* GEN END TAG OUTSIDE LET *)
  	       (* GEN BEGIN TAG OUTSIDE LET *) val c = b div 2 (* GEN END TAG OUTSIDE LET *)
  	       (* GEN BEGIN TAG OUTSIDE LET *) val d = b + c (* GEN END TAG OUTSIDE LET *)
  	     in
  	       num(a)+128*(num(b)+128*(num(c)+128*num(d)))
  	     end
      end
end;  (* structure StringHash *)

structure StringHashTable
  :> TABLE where type key = string =
  HashTable (type key' = string
	     (* GEN BEGIN TAG OUTSIDE LET *) val hash = StringHash.stringHash (* GEN END TAG OUTSIDE LET *)
	     (* GEN BEGIN TAG OUTSIDE LET *) val eq = (op =) (* GEN END TAG OUTSIDE LET *));
