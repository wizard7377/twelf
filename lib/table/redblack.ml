(* Red/Black Trees *)

(* Author: Frank Pfenning *)

module RedBlackTree (K : sig
  type t

  val compare : K.t * K.t -> order
end) : Table.TABLE with type key = K.t = struct
  type key = K.t
  type 'a entry = key * 'a

  type 'a dict =
    | Empty
    | Red of 'a entry * 'a dict * 'a dict
    | Black of 'a entry * 'a dict * 'a dict

  type 'a table = 'a dict ref
  (* Representation Invariants *)

  (*
     1. The tree is ordered: for_sml every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a Leaf has the same number of
        black nodes, called the black height of the tree.
  *)

  let rec lookup dict key =
    let rec lk = function
      | Empty -> None
      | Red tree -> lk' tree
      | Black tree -> lk' tree
    and lk' ((key1, datum1), left, right) =
      match K.compare (key, key1) with
      | Eq -> Some datum1
      | Lt -> lk left
      | Gt -> lk right
    in
    lk dict
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

  let rec restore_right = function
    | Black (e, Red lt, Red rt) -> Red (e, Black lt, Black rt)
    | Black (e, Red lt, Red rt) -> Red (e, Black lt, Black rt)
    | Black (e, l, Red (re, Red (rle, rll, rlr), rr)) ->
        Black (rle, Red (e, l, rll), Red (re, rlr, rr))
    | Black (e, l, Red (re, rl, rr)) -> Black (re, Red (e, l, rl), rr)
    | dict -> dict
  (* restore_left is like restore_right, except *)

  (* the color invariant may be violated only at the root of left child *)

  let rec restore_left = function
    | Black (e, Red lt, Red rt) -> Red (e, Black lt, Black rt)
    | Black (e, Red lt, Red rt) -> Red (e, Black lt, Black rt)
    | Black (e, Red (le, ll, lr), r) -> Black (le, ll, Red (e, lr, r))
    | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r) ->
        Black (lre, Red (le, ll, lrl), Red (e, lrr, r))
    | dict -> dict

  let rec insert (dict, entry) =
    (* val ins : 'a dict -> 'a dict  inserts entry *)
    (* ins (Red _) may violate color invariant at root *)
    (* ins (Black _) or ins (Empty) will be red/black tree *)
    (* ins preserves black height *)
    let rec ins = function
      | Empty -> Red (entry, Empty, Empty)
      | Red (entry1, left, right) -> (
          match K.compare (key, key1) with
          | Eq -> Red (entry, left, right)
          | Lt -> Red (entry1, ins left, right)
          | Gt -> Red (entry1, left, ins right))
      | Black (entry1, left, right) -> (
          match K.compare (key, key1) with
          | Eq -> Black (entry, left, right)
          | Lt -> restore_left (Black (entry1, ins left, right))
          | Gt -> restore_right (Black (entry1, left, ins right)))
    in
    match ins dict with
    | Red t -> Black t (* re-color *)
    | Red t -> Black t (* re-color *)
    | dict -> dict
  (* use non-imperative version? *)

  let rec insertShadow (dict, entry) =
    (* : 'a entry option ref *)
    let oldEntry = ref None in
    let rec ins = function
      | Empty -> Red (entry, Empty, Empty)
      | Red (entry1, left, right) -> (
          match K.compare (key, key1) with
          | Eq ->
              oldEntry := Some entry1;
              Red (entry, left, right)
          | Lt -> Red (entry1, ins left, right)
          | Gt -> Red (entry1, left, ins right))
      | Black (entry1, left, right) -> (
          match K.compare (key, key1) with
          | Eq ->
              oldEntry := Some entry1;
              Black (entry, left, right)
          | Lt -> restore_left (Black (entry1, ins left, right))
          | Gt -> restore_right (Black (entry1, left, ins right)))
    in
    oldEntry := None;
    ( (match ins dict with
      | Red t -> Black t (* re-color *)
      | Red t -> Black t (* re-color *)
      | dict -> dict),
      !oldEntry )

  let rec app f dict =
    let rec ap = function
      | Empty -> ()
      | Red tree -> ap' tree
      | Black tree -> ap' tree
    and ap' (entry1, left, right) =
      ap left;
      f entry1;
      ap right
    in
    ap dict

  let rec new_ n = ref Empty
  (* ignore size hint *)

  let insert = fun table -> fun entry -> table := insert (!table, entry)

  let insertShadow =
   fun table ->
    fun entry ->
     let dict, oldEntry = insertShadow (!table, entry) in
     table := dict;
     oldEntry

  let lookup = fun table -> fun key -> lookup !table key
  let clear = fun table -> table := Empty
  let app = fun f -> fun table -> app f !table
end

(* functor RedBlackTree *)

module StringRedBlackTree = RedBlackTree
module IntRedBlackTree = RedBlackTree
