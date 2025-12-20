(* Persistent red/black trees *)


(* Specialized for_sml subordination *)


(* Author: Frank Pfenning *)


(* Copied from src/table/red-black-tree.fun *)


module type INTSET = sig
  type intset
  val empty : intset
  val insert : int * intset -> intset
  val member : int * intset -> bool
  val foldl : (int * 'b -> 'b) -> 'b -> intset -> 'b

end


module IntSet : INTSET = struct type rbt = Empty | Red of int * rbt * rbt | Black of int * rbt * rbt
(* Representation Invariants *)

(*
     1. The tree is ordered: for_sml every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)

let rec lookup dict x  = ( let rec lk = function (Empty) -> false | (Red tree) -> lk' tree | (Black tree) -> lk' tree
and lk' (x1, left, right)  = (match Int.compare (x, x1) with Eq -> true | Lt -> lk left | Gt -> lk right) in  lk dict )
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

let rec restore_right = function (Black (e, Red lt, Red (rt))) -> Red (e, Black lt, Black rt) | (Black (e, Red lt, Red (rt))) -> Red (e, Black lt, Black rt) | (Black (e, l, Red (re, Red (rle, rll, rlr), rr))) -> Black (rle, Red (e, l, rll), Red (re, rlr, rr)) | (Black (e, l, Red (re, rl, rr))) -> Black (re, Red (e, l, rl), rr) | dict -> dict
(* restore_left is like restore_right, except *)

(* the color invariant may be violated only at the root of left child *)

let rec restore_left = function (Black (e, Red (lt), Red rt)) -> Red (e, Black lt, Black rt) | (Black (e, Red (lt), Red rt)) -> Red (e, Black lt, Black rt) | (Black (e, Red (le, ll, lr), r)) -> Black (le, ll, Red (e, lr, r)) | (Black (e, Red (le, ll, Red (lre, lrl, lrr)), r)) -> Black (lre, Red (le, ll, lrl), Red (e, lrr, r)) | dict -> dict
let rec insert (dict, x)  = ( (* val ins : 'a dict -> 'a dict  inserts entry *)
(* ins (Red _) may violate color invariant at root *)
(* ins (Black _) or ins (Empty) will be red/black tree *)
(* ins preserves black height *)
let rec ins = function (Empty) -> Red (x, Empty, Empty) | (Red (x1, left, right)) -> (match Int.compare (x, x1) with Eq -> Red (x, left, right) | Lt -> Red (x1, ins left, right) | Gt -> Red (x1, left, ins right)) | (Black (x1, left, right)) -> (match Int.compare (x, x1) with Eq -> Black (x, left, right) | Lt -> restore_left (Black (x1, ins left, right)) | Gt -> restore_right (Black (x1, left, ins right))) in  match ins dict with Red (t) -> Black t(* re-color *)
 | Red (t) -> Black t(* re-color *)
 | dict -> dict )
type intset = rbt
let empty = Empty
let insert = fun (x, t) -> insert (t, x)
let member = fun (x, t) -> lookup t x
let rec foldl f a t  = ( let rec fo = function (Empty, r) -> r | (Red (x, left, right), r) -> fo (right, f (x, fo (left, r))) | (Black (x, left, right), r) -> fo (right, f (x, fo (left, r))) in  fo (t, a) )
 end


(* structure IntSet *)

