(* Persistent red/black trees *)
(* Specialized for subordination *)
(* Author: Frank Pfenning *)
(* Copied from src/table/red-black-tree.fun *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature INTSET =
sig
  type intset
  val empty : intset
  val insert : int * intset -> intset
  val member : int * intset -> bool
  val foldl : (int * 'b -> 'b) -> 'b -> intset -> 'b
end (* GEN END SIGNATURE DECLARATION *);

structure IntSet :> INTSET =
struct

  datatype rbt =
    Empty				(* considered black *)
  | Red of int * rbt * rbt
  | Black of int * rbt * rbt

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

  fun lookup dict x =
    let
      fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) lk (Empty) = false (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
  	| (* GEN BEGIN CASE BRANCH *) lk (Red tree) = lk' tree (* GEN END CASE BRANCH *)
        | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) lk (Black tree) = lk' tree (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
      and lk' (x1, left, right) =
  	    (case Int.compare(x,x1)
  	       of EQUAL => true
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
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) restore_right (Black(e, Red lt, Red (rt as (_,Red _,_)))) =
         Red(e, Black lt, Black rt) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)	(* re-color *)
    | (* GEN BEGIN CASE BRANCH *) restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt) (* GEN END CASE BRANCH *)	(* re-color *)
    | (* GEN BEGIN CASE BRANCH *) restore_right (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) =
    	 (* l is black, deep rotate *)
    	 Black(rle, Red(e, l, rll), Red(re, rlr, rr)) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) restore_right (Black(e, l, Red(re, rl, rr as Red _))) =
    	 (* l is black, shallow rotate *)
    	 Black(re, Red(e, l, rl), rr) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) restore_right dict = dict (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) restore_left (Black(e, Red (lt as (_,Red _,_)), Red rt)) =
  	 Red(e, Black lt, Black rt) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)	(* re-color *)
    | (* GEN BEGIN CASE BRANCH *) restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
    	 Red(e, Black lt, Black rt) (* GEN END CASE BRANCH *)	(* re-color *)
    | (* GEN BEGIN CASE BRANCH *) restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
    	 (* r is black, shallow rotate *)
    	 Black(le, ll, Red(e, lr, r)) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
    	 (* r is black, deep rotate *)
    	 Black(lre, Red(le, ll, lrl), Red(e, lrr, r)) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) restore_left dict = dict (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  fun insert (dict, x) =
    let
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) ins (Empty) = Red(x, Empty, Empty) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
  	| (* GEN BEGIN CASE BRANCH *) ins (Red(x1, left, right)) =
  	  (case Int.compare(x,x1)
  	     of EQUAL => Red(x, left, right)
  	      | LESS => Red(x1, ins left, right)
  	      | GREATER => Red(x1, left, ins right)) (* GEN END CASE BRANCH *)
  	| (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) ins (Black(x1, left, right)) =
  	  (case Int.compare(x,x1)
  	     of EQUAL => Black(x, left, right)
  	      | LESS => restore_left (Black(x1, ins left, right))
  	      | GREATER => restore_right (Black(x1, left, ins right))) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    in
      case ins dict
  	of Red (t as (_, Red _, _)) => Black t (* re-color *)
  	 | Red (t as (_, _, Red _)) => Black t (* re-color *)
  	 | dict => dict
    end
  in
    type intset = rbt
    (* GEN BEGIN TAG OUTSIDE LET *) val empty = Empty (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insert = (* GEN BEGIN FUNCTION EXPRESSION *) fn (x,t) => insert (t, x) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val member = (* GEN BEGIN FUNCTION EXPRESSION *) fn (x,t) => lookup t x (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    fun foldl f a t =
        let fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) fo (Empty, r) = r (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
              | (* GEN BEGIN CASE BRANCH *) fo (Red (x, left, right), r) =
                  	          fo (right, f (x, fo (left, r))) (* GEN END CASE BRANCH *)
              | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) fo (Black (x, left, right), r) =
                  		  fo (right, f (x, fo (left, r))) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)
    	in
    	  fo (t, a)
    	end
  end

end;  (* structure IntSet *)
