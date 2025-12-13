(* Red/Black Trees *)
(* Author: Frank Pfenning *)

functor (* GEN BEGIN FUNCTOR DECL *) RedBlackTree
  (type key'
   val compare : key' * key' -> order)
  :> TABLE where type key = key' =
struct
  type key = key'
  type 'a entry = key * 'a

  datatype 'a dict =
    Empty				(* considered black *)
  | Red of 'a entry * 'a dict * 'a dict
  | Black of 'a entry * 'a dict * 'a dict

  type 'a table = 'a dict ref

  (* Representation Invariants *)
  (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)

  local

  fun lookup dict key =
    let
      fun (* GEN BEGIN FUN FIRST *) lk (Empty) = NONE (* GEN END FUN FIRST *)
  	| (* GEN BEGIN FUN BRANCH *) lk (Red tree) = lk' tree (* GEN END FUN BRANCH *)
        | (* GEN BEGIN FUN BRANCH *) lk (Black tree) = lk' tree (* GEN END FUN BRANCH *)
      and lk' ((key1, datum1), left, right) =
  	    (case compare(key,key1)
  	       of EQUAL => SOME(datum1)
  	        | LESS => lk left
  		| GREATER => lk right)
      in
  	lk dict
      end

  (* val restore_right : 'a dict -> 'a dict *)
  (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
  fun (* GEN BEGIN FUN FIRST *) restore_right (Black(e, Red lt, Red (rt as (_,Red _,_)))) =
         Red(e, Black lt, Black rt) (* GEN END FUN FIRST *)	(* re-color *)
    | (* GEN BEGIN FUN BRANCH *) restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt) (* GEN END FUN BRANCH *)	(* re-color *)
    | (* GEN BEGIN FUN BRANCH *) restore_right (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) =
    	 (* l is black, deep rotate *)
    	 Black(rle, Red(e, l, rll), Red(re, rlr, rr)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) restore_right (Black(e, l, Red(re, rl, rr as Red _))) =
    	 (* l is black, shallow rotate *)
    	 Black(re, Red(e, l, rl), rr) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) restore_right dict = dict (* GEN END FUN BRANCH *)

  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  fun (* GEN BEGIN FUN FIRST *) restore_left (Black(e, Red (lt as (_,Red _,_)), Red rt)) =
  	 Red(e, Black lt, Black rt) (* GEN END FUN FIRST *)	(* re-color *)
    | (* GEN BEGIN FUN BRANCH *) restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
    	 Red(e, Black lt, Black rt) (* GEN END FUN BRANCH *)	(* re-color *)
    | (* GEN BEGIN FUN BRANCH *) restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
    	 (* r is black, shallow rotate *)
    	 Black(le, ll, Red(e, lr, r)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
    	 (* r is black, deep rotate *)
    	 Black(lre, Red(le, ll, lrl), Red(e, lrr, r)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) restore_left dict = dict (* GEN END FUN BRANCH *)

  fun insert (dict, entry as (key,datum)) =
    let
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      fun (* GEN BEGIN FUN FIRST *) ins (Empty) = Red(entry, Empty, Empty) (* GEN END FUN FIRST *)
  	| (* GEN BEGIN FUN BRANCH *) ins (Red(entry1 as (key1, datum1), left, right)) =
  	  (case compare(key,key1)
  	     of EQUAL => Red(entry, left, right)
  	      | LESS => Red(entry1, ins left, right)
  	      | GREATER => Red(entry1, left, ins right)) (* GEN END FUN BRANCH *)
  	| (* GEN BEGIN FUN BRANCH *) ins (Black(entry1 as (key1, datum1), left, right)) =
  	  (case compare(key,key1)
  	     of EQUAL => Black(entry, left, right)
  	      | LESS => restore_left (Black(entry1, ins left, right))
  	      | GREATER => restore_right (Black(entry1, left, ins right))) (* GEN END FUN BRANCH *)
    in
      case ins dict
  	of Red (t as (_, Red _, _)) => Black t (* re-color *)
  	 | Red (t as (_, _, Red _)) => Black t (* re-color *)
  	 | dict => dict
    end

  (* use non-imperative version? *)
  fun insertShadow (dict, entry as (key,datum)) =
      let (* GEN BEGIN TAG OUTSIDE LET *) val oldEntry = ref NONE (* GEN END TAG OUTSIDE LET *) (* : 'a entry option ref *)
          fun (* GEN BEGIN FUN FIRST *) ins (Empty) = Red(entry, Empty, Empty) (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) ins (Red(entry1 as (key1, datum1), left, right)) =
  	      (case compare(key,key1)
  		 of EQUAL => (oldEntry := SOME(entry1);
  			      Red(entry, left, right))
  	          | LESS => Red(entry1, ins left, right)
  	          | GREATER => Red(entry1, left, ins right)) (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) ins (Black(entry1 as (key1, datum1), left, right)) =
  	      (case compare(key,key1)
  		 of EQUAL => (oldEntry := SOME(entry1);
  			      Black(entry, left, right))
  	          | LESS => restore_left (Black(entry1, ins left, right))
  	          | GREATER => restore_right (Black(entry1, left, ins right))) (* GEN END FUN BRANCH *)
      in
  	(oldEntry := NONE;
  	 ((case ins dict
  	     of Red (t as (_, Red _, _)) => Black t (* re-color *)
  	      | Red (t as (_, _, Red _)) => Black t (* re-color *)
  	      | dict => dict),
  	  !oldEntry))
      end
  
  fun app f dict =
      let fun (* GEN BEGIN FUN FIRST *) ap (Empty) = () (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Red tree) = ap' tree (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Black tree) = ap' tree (* GEN END FUN BRANCH *)
  	  and ap' (entry1, left, right) =
  	      (ap left; f entry1; ap right)
      in
  	ap dict
      end

  in
    fun new (n) = ref (Empty) (* ignore size hint *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insert = ((* GEN BEGIN FUNCTION EXPRESSION *) fn table => (* GEN BEGIN FUNCTION EXPRESSION *) fn entry => (table := insert (!table, entry)) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insertShadow =
        ((* GEN BEGIN FUNCTION EXPRESSION *) fn table => (* GEN BEGIN FUNCTION EXPRESSION *) fn entry => 
            	 let
            	   (* GEN BEGIN TAG OUTSIDE LET *) val (dict, oldEntry) = insertShadow (!table, entry) (* GEN END TAG OUTSIDE LET *)
            	 in
            	   (table := dict; oldEntry)
            	 end (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val lookup = ((* GEN BEGIN FUNCTION EXPRESSION *) fn table => (* GEN BEGIN FUNCTION EXPRESSION *) fn key => lookup (!table) key (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val clear = ((* GEN BEGIN FUNCTION EXPRESSION *) fn table => (table := Empty) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val app = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => (* GEN BEGIN FUNCTION EXPRESSION *) fn table => app f (!table) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  end

end (* GEN END FUNCTOR DECL *);  (* functor RedBlackTree *)

structure StringRedBlackTree =
  RedBlackTree (type key' = string
		(* GEN BEGIN TAG OUTSIDE LET *) val compare = String.compare (* GEN END TAG OUTSIDE LET *)) 

structure IntRedBlackTree =
  RedBlackTree (type key' = int
		(* GEN BEGIN TAG OUTSIDE LET *) val compare = Int.compare (* GEN END TAG OUTSIDE LET *)) 
