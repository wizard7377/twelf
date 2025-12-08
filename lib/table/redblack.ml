(* Red/Black Trees *)
(* Author: Frank Pfenning *)

module RedBlackTree
  (type key'
   let compare : key' * key' -> order)
  :> TABLE where type key = key' =
struct
  type key = key'
  type 'a entry = key * 'a

  type 'a dict =
    Empty				(* considered black *)
  | Red of 'a entry * 'a dict * 'a dict
  | Black of 'a entry * 'a dict * 'a dict

  type 'a Table = 'a dict ref

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
      let rec lk = function (Empty) -> NONE
	| (Red tree) -> lk' tree
        | (Black tree) -> lk' tree
      and lk' ((key1, datum1), left, right) =
	    (case compare(key,key1)
	       of EQUAL => SOME(datum1)
	        | LESS => lk left
		| GREATER => lk right)
      in
	lk dict
      end

  (* let restore_right : 'a dict -> 'a dict *)
  (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
  let rec restore_right = function (Black(e, Red lt, Red (rt as (_,Red _,_)))) -> 
         Red(e, Black lt, Black rt)	(* re-color *)
    | (Black(e, Red lt, Red (rt as (_,_,Red _)))) -> 
         Red(e, Black lt, Black rt)	(* re-color *)
    | (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) -> 
	 (* l is black, deep rotate *)
	 Black(rle, Red(e, l, rll), Red(re, rlr, rr))
    | restore_right (Black(e, l, Red(re, rl, rr as Red _))) =
	 (* l is black, shallow rotate *)
	 Black(re, Red(e, l, rl), rr)
    | restore_right dict = dict

  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  fun restore_left (Black(e, Red (lt as (_,Red _,_)), Red rt)) =
	 Red(e, Black lt, Black rt)	(* re-color *)
    | restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
	 Red(e, Black lt, Black rt)	(* re-color *)
    | restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
	 (* r is black, shallow rotate *)
	 Black(le, ll, Red(e, lr, r))
    | restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
	 (* r is black, deep rotate *)
	 Black(lre, Red(le, ll, lrl), Red(e, lrr, r))
    | restore_left dict = dict

  fun insert (dict, entry as (key,datum)) =
    let
      (* let ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      let rec ins = function (Empty) -> Red(entry, Empty, Empty)
	| (Red(entry1 as (key1, datum1), left, right)) -> 
	  (case compare(key,key1)
	     of EQUAL => Red(entry, left, right)
	      | LESS => Red(entry1, ins left, right)
	      | GREATER => Red(entry1, left, ins right))
	| ins (Black(entry1 as (key1, datum1), left, right)) =
	  (case compare(key,key1)
	     of EQUAL => Black(entry, left, right)
	      | LESS => restore_left (Black(entry1, ins left, right))
	      | GREATER => restore_right (Black(entry1, left, ins right)))
    in
      case ins dict
	of Red (t as (_, Red _, _)) => Black t (* re-color *)
	 | Red (t as (_, _, Red _)) => Black t (* re-color *)
	 | dict => dict
    end

  (* use non-imperative version? *)
  fun insertShadow (dict, entry as (key,datum)) =
      let let oldEntry = ref NONE (* : 'a entry option ref *)
          let rec ins = function (Empty) -> Red(entry, Empty, Empty)
	    | (Red(entry1 as (key1, datum1), left, right)) -> 
	      (case compare(key,key1)
		 of EQUAL => (oldEntry := SOME(entry1);
			      Red(entry, left, right))
	          | LESS => Red(entry1, ins left, right)
	          | GREATER => Red(entry1, left, ins right))
	    | ins (Black(entry1 as (key1, datum1), left, right)) =
	      (case compare(key,key1)
		 of EQUAL => (oldEntry := SOME(entry1);
			      Black(entry, left, right))
	          | LESS => restore_left (Black(entry1, ins left, right))
	          | GREATER => restore_right (Black(entry1, left, ins right)))
      in
	(oldEntry := NONE;
	 ((case ins dict
	     of Red (t as (_, Red _, _)) => Black t (* re-color *)
	      | Red (t as (_, _, Red _)) => Black t (* re-color *)
	      | dict => dict),
	  !oldEntry))
      end
  
  fun app f dict =
      let fun ap (Empty) = ()
	    | ap (Red tree) = ap' tree
	    | ap (Black tree) = ap' tree
	  and ap' (entry1, left, right) =
	      (ap left; f entry1; ap right)
      in
	ap dict
      end

  in
    fun new (n) = ref (Empty) (* ignore size hint *)
    let insert = (fun table -> fun entry -> (table := insert (!table, entry)))
    let insertShadow =
        (fun table -> fun entry -> 
	 let
	   let (dict, oldEntry) = insertShadow (!table, entry)
	 in
	   (table := dict; oldEntry)
	 end)
    let lookup = (fun table -> fun key -> lookup (!table) key)
    let clear = (fun table -> (table := Empty))
    let app = (fun f -> fun table -> app f (!table))
  end

end;; (* functor RedBlackTree *)

module StringRedBlackTree =
  RedBlackTree (type key' = string
		let compare = String.compare) 

module IntRedBlackTree =
  RedBlackTree (type key' = int
		let compare = Int.compare) 
