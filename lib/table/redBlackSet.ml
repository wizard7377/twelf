open Basis

(* Sets *)

(* Author: Brigitte Pientka *)

(* This provides a common interface to ordered sets *)

(* based on red/black trees *)

module type RBSET = sig
  type key = int

  (* parameter *)
  type 'a entry = key * 'a

  exception Error of string

  type 'a ordSet

  val new_ : unit -> 'a ordSet
  val copy : 'a ordSet -> 'a ordSet
  val insert : 'a ordSet -> 'a entry -> unit
  val insertList : 'a ordSet -> 'a entry list -> unit
  val insertShadow : 'a ordSet -> 'a entry -> unit
  val insertLast : 'a ordSet -> 'a -> unit

  (*  val delete : 'a ordSet -> key -> unit*)
  val lookup : 'a ordSet -> key -> 'a option
  val isEmpty : 'a ordSet -> bool
  val last : 'a ordSet -> 'a entry
  val clear : 'a ordSet -> unit

  (* Applies f:'a -> unit to all entries in the set
     pre-order traversal *)
  val app : 'a ordSet -> ('a -> unit) -> unit
  val update : 'a ordSet -> ('a -> 'a) -> 'a ordSet

  (* Applies f:'a entry -> unit to all entries in the set
     pre-order traversal *)
  val forall : 'a ordSet -> ('a entry -> unit) -> unit

  (*  val exists : 'a ordSet -> ('a entry -> 'b option) -> ('a entry (* key * 'a *) * 'b) option *)
  val exists : 'a ordSet -> ('a entry -> bool) -> bool
  val existsOpt : 'a ordSet -> ('a -> bool) -> int option
  val size : 'a ordSet -> int
  val union : 'a ordSet -> 'a ordSet -> 'a ordSet
  val difference : 'a ordSet -> 'a ordSet -> 'a ordSet
  val difference2 : 'a ordSet -> 'a ordSet -> 'a ordSet * 'a ordSet

  val differenceModulo :
    'a ordSet -> 'b ordSet -> ('a -> 'b -> unit) -> 'a ordSet * 'b ordSet

  (* splits two sets into S1, S2, S3 *)
  val splitSets :
    'a ordSet ->
    'a ordSet ->
    ('a -> 'a -> 'a option) ->
    'a ordSet * 'a ordSet * 'a ordSet

  val intersection : 'a ordSet -> 'a ordSet -> 'a ordSet
end

(* signature RBSET *)
(* redblack-set.sml
 *
 * This code is based on Chris Okasaki's implementation of
 * red-black trees.  The linear-time tree construction code is
 * based on the paper "Constructing red-black trees" by Hinze,
 * and the delete function is based on the description in Cormen,
 * Leiserson, and Rivest.
 *
 * A red-black tree should satisfy the following two invariants:
 *
 *   Red Invariant: each red node has a black parent.
 *
 *   Black Condition: each path from the root to an empty node has the
 *     same number of black nodes (the tree's black height).
 *
 * The Red condition implies that the root is always black and the Black
 * condition implies that any node with only one child will be black and
 * its child will be a red Leaf.
 *)

module RBSet : RBSET = struct
  type key = int
  type 'a entry = key * 'a

  type 'a dict =
    | Empty
    | Red of 'a entry * 'a dict * 'a dict
    | Black of 'a entry * 'a dict * 'a dict

  type 'a set = Set of (int * 'a dict)

  exception Error of string

  type 'a ordSet = 'a set ref

  let rec isEmpty = function Set (_, Empty) -> true | Set (_, _) -> false
  let empty = Set (0, Empty)
  let rec singleton x = Set (1, Red (x, Empty, Empty))
  let compare (a, b) = Integer.compare a b
  (* Representation Invariants *)

  (*
     1. The tree is ordered: for_sml every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is Less than
        key1 and every key in right is Greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a Leaf has the same number of
        black nodes, called the black height of the tree.
  *)

  let rec lookup (Set (n, dict)) key =
    let rec lk = function
      | Empty -> None
      | Red (entry, left, right) -> lk' (entry, left, right)
      | Black (entry, left, right) -> lk' (entry, left, right)
    and lk' ((key1, datum1), left, right) =
      match compare (key, key1) with
      | Equal -> Some datum1
      | Less -> lk left
      | Greater -> lk right
    in
    lk dict

  let rec last (Set (n, dict)) = (n, Option.valOf (lookup (Set (n, dict)) n))
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
    | Black (e, Red (le, ll, lr), Red (re, rl, rr)) ->
        Red (e, Black (le, ll, lr), Black (re, rl, rr))
    | Black (e, l, Red (re, Red (rle, rll, rlr), rr)) ->
        Black (rle, Red (e, l, rll), Red (re, rlr, rr))
    | Black (e, l, Red (re, rl, rr)) -> Black (re, Red (e, l, rl), rr)
    | dict -> dict
  (* restore_left is like restore_right, except *)

  (* the color invariant may be violated only at the root of left child *)

  let rec restore_left = function
    | Black (e, Red (le, ll, lr), Red (re, rl, rr)) ->
        Red (e, Black (le, ll, lr), Black (re, rl, rr))
    | Black (e, Red (le, ll, lr), r) -> Black (le, ll, Red (e, lr, r))
    | Black (e, Red (le, ll, Red (lre, lrl, lrr)), r) ->
        Black (lre, Red (le, ll, lrl), Red (e, lrr, r))
    | dict -> dict

  let rec insert (Set (n, dict), entry) =
    (* val ins : 'a dict -> 'a dict  inserts entry *)
    (* ins (Red _) may violate color invariant at root *)
    (* ins (Black _) or ins (Empty) will be red/black tree *)
    (* ins preserves black height *)
    let key, _ = entry in
    let nItems = ref n in
    let rec ins = function
      | Empty ->
          nItems := n + 1;
          Red (entry, Empty, Empty)
      | Red (((key1, _) as entry1), left, right) -> (
          match compare (key, key1) with
          | Equal ->
              (*print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n");*)
              Red (entry1, left, right)
          | Less -> Red (entry1, ins left, right)
          | Greater -> Red (entry1, left, ins right))
      | Black (((key1, _) as entry1), left, right) -> (
          match compare (key, key1) with
          | Equal ->
              (* print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n"); *)
              Black (entry1, left, right)
          | Less -> restore_left (Black (entry1, ins left, right))
          | Greater -> restore_right (Black (entry1, left, ins right)))
    in
    let dict' =
      match ins dict with
      | Red (e, l, r) -> Black (e, l, r) (* re-color *)
      | dict -> dict
    in
    Set (!nItems, dict')

  let rec insertList = function
    | s, [] -> s
    | s, e :: list -> insertList (insert (s, e), list)

  let rec insertLast (Set (n, dict), datum) =
    let (Set (n', dic')) = insert (Set (n, dict), (n + 1, datum)) in
    Set (n', dic')
  (* input: set sc
     output set s' *)

  let rec insertShadow (Set (n, dict), entry) =
    (* : 'a entry option ref *)
    let key, _ = entry in
    let oldEntry = ref None in
    let rec ins = function
      | Empty -> Red (entry, Empty, Empty)
      | Red (((key1, _) as entry1), left, right) -> (
          match compare (key, key1) with
          | Equal ->
              oldEntry := Some entry1;
              Red (entry, left, right)
          | Less -> Red (entry1, ins left, right)
          | Greater -> Red (entry1, left, ins right))
      | Black (((key1, _) as entry1), left, right) -> (
          match compare (key, key1) with
          | Equal ->
              oldEntry := Some entry1;
              Black (entry, left, right)
          | Less -> restore_left (Black (entry1, ins left, right))
          | Greater -> restore_right (Black (entry1, left, ins right)))
    in
    let dict', oldEntry' =
      oldEntry := None;
      ( (match ins dict with
        | Red (e, l, r) -> Black (e, l, r) (* re-color *)
        | dict -> dict),
        !oldEntry )
    in
    Set (n, dict')
  (* Remove an item.  Raises LibBase.NotFound if not found. *)

  type color = RedColor | BlackColor

  type 'a zipper =
    | Top
    | LeftRed of ('a entry * 'a dict * 'a zipper)
    | LeftBlack of ('a entry * 'a dict * 'a zipper)
    | RightRed of ('a dict * 'a entry * 'a zipper)
    | RightBlack of ('a dict * 'a entry * 'a zipper)

  let rec delete (Set (nItems, t), k) =
    (* bbZip propagates a black deficit up the tree until either the top
     * is reached, or the deficit can be covered.  It returns a boolean
     * that is true if there is still a deficit and the zipped tree.
     *)
    let rec zip = function
      | Top, t -> t
      | LeftRed (x, b, z), a -> zip (z, Red (x, a, b))
      | LeftBlack (x, b, z), a -> zip (z, Black (x, a, b))
      | RightRed (a, x, z), b -> zip (z, Red (x, a, b))
      | RightBlack (a, x, z), b -> zip (z, Black (x, a, b))
    in
    let rec bbZip = function
      | Top, t -> (true, t)
      | LeftBlack (x, Red (y, c, d), z), a ->
          bbZip (LeftRed (x, c, LeftBlack (y, d, z)), a)
      | LeftRed (x, Red (y, c, d), z), a ->
          bbZip (LeftRed (x, c, LeftBlack (y, d, z)), a)
      | LeftBlack (x, Black (w, Red (y, c, d), e), z), a ->
          bbZip (LeftBlack (x, Black (y, c, Red (w, d, e)), z), a)
      | LeftRed (x, Black (w, Red (y, c, d), e), z), a ->
          bbZip (LeftRed (x, Black (y, c, Red (w, d, e)), z), a)
      | LeftBlack (x, Black (y, c, Red (w, d, e)), z), a ->
          (false, zip (z, Black (y, Black (x, a, c), Black (w, d, e))))
      | LeftRed (x, Black (y, c, Red (w, d, e)), z), a ->
          (false, zip (z, Red (y, Black (x, a, c), Black (w, d, e))))
      | LeftRed (x, Black (y, c, d), z), a ->
          (false, zip (z, Black (x, a, Red (y, c, d))))
      | LeftBlack (x, Black (y, c, d), z), a ->
          bbZip (z, Black (x, a, Red (y, c, d)))
      | RightBlack (Red (y, c, d), x, z), b ->
          bbZip (RightRed (d, x, RightBlack (c, y, z)), b)
      | RightRed (Red (y, c, d), x, z), b ->
          bbZip (RightRed (d, x, RightBlack (c, y, z)), b)
      | RightBlack (Black (y, Red (w, c, d), e), x, z), b ->
          bbZip (RightBlack (Black (w, c, Red (y, d, e)), x, z), b)
      | RightRed (Black (y, Red (w, c, d), e), x, z), b ->
          bbZip (RightRed (Black (w, c, Red (y, d, e)), x, z), b)
      | RightBlack (Black (y, c, Red (w, d, e)), x, z), b ->
          (false, zip (z, Black (y, c, Black (x, Red (w, d, e), b))))
      | RightRed (Black (y, c, Red (w, d, e)), x, z), b ->
          (false, zip (z, Red (y, c, Black (x, Red (w, d, e), b))))
      | RightRed (Black (y, c, d), x, z), b ->
          (false, zip (z, Black (x, Red (y, c, d), b)))
      | RightBlack (Black (y, c, d), x, z), b ->
          bbZip (z, Black (x, Red (y, c, d), b))
      | z, t -> (false, zip (z, t))
    in
    let rec delMin = function
      | Red (y, Empty, b), z -> (y, (false, zip (z, b)))
      | Black (y, Empty, b), z -> (y, bbZip (z, b))
      | Red (y, a, b), z -> delMin (a, LeftRed (y, b, z))
      | Black (y, a, b), z -> delMin (a, LeftBlack (y, b, z))
    in
    let rec joinBlack = function
      | a, Empty, z -> snd (bbZip (z, a))
      | Empty, b, z -> snd (bbZip (z, b))
      | a, b, z ->
          let x, (needB, b') = delMin (b, Top) in
          if needB then snd (bbZip (z, Black (x, a, b')))
          else zip (z, Black (x, a, b'))
    in
    let rec joinRed = function
      | Empty, Empty, z -> zip (z, Empty)
      | a, b, z ->
          let x, (needB, b') = delMin (b, Top) in
          if needB then snd (bbZip (z, Red (x, a, b')))
          else zip (z, Red (x, a, b'))
    in
    let rec del = function
      | Empty, z -> raise (Error "not found\n")
      | Red (((k', _) as y), a, b), z -> (
          match compare (k, k') with
          | Less -> del (a, LeftRed (y, b, z))
          | Equal -> joinRed (a, b, z)
          | Greater -> del (b, RightRed (a, y, z)) (* end case *))
      | Black (((k', _) as y), a, b), z -> (
          match compare (k, k') with
          | Less -> del (a, LeftBlack (y, b, z))
          | Equal -> joinBlack (a, b, z)
          | Greater -> del (b, RightBlack (a, y, z)) (* end case *))
    in
    Set (nItems - 1, del (t, Top))
  (* local *)

  (* does not apply f to all elements of S in order! *)

  let rec app f (Set (n, dict)) =
    let rec ap = function
      | Empty -> ()
      | Red (entry, left, right) -> ap' (entry, left, right)
      | Black (entry, left, right) -> ap' (entry, left, right)
    and ap' ((_, datum), left, right) =
      ap left;
      f datum;
      ap right
    in
    ap dict

  let rec update f (Set (n, dict)) =
    let rec upd = function
      | Empty -> Empty
      | Red (entry, left, right) ->
          let entry', left', right' = upd' (entry, left, right) in
          Red (entry', left', right')
      | Black (entry, left, right) ->
          let entry', left', right' = upd' (entry, left, right) in
          Black (entry', left', right')
    and upd' ((k, datum), left, right) =
      let left' = upd left in
      let datum' = f datum in
      let right' = upd right in
      ((k, datum'), left', right')
    in
    Set (n, upd dict)

  let rec forall (Set (n, dict)) f =
    let rec ap = function
      | Empty -> ()
      | Red (entry, left, right) -> ap' (entry, left, right)
      | Black (entry, left, right) -> ap' (entry, left, right)
    and ap' (entry, left, right) =
      ap left;
      f entry;
      ap right
    in
    ap dict

  let rec existsOpt (Set (n, dict)) f =
    let rec ap = function
      | Empty -> None
      | Red (entry, left, right) -> ap' (entry, left, right)
      | Black (entry, left, right) -> ap' (entry, left, right)
    and ap' ((k, d), left, right) =
      if f d then (
        print "SUCCESS\n";
        Some k)
      else (
        print "FAILED\n";
        match ap left with None -> ap right | Some res -> Some res)
    in
    ap dict

  let rec exists (Set (n, dict)) f =
    let rec ap = function
      | Empty -> false
      | Red (entry, left, right) -> ap' (entry, left, right)
      | Black (entry, left, right) -> ap' (entry, left, right)
    and ap' (entry, left, right) =
      if f entry then true else if ap left then true else ap right
    in
    ap dict

  let rec setsize (Set (n, _)) = n
  (* support for_sml constructing red-black trees in linear time from increasing
   * ordered sequences (based on a description by R. Hinze).  Note that the
   * elements in the digits are ordered with the largest on the left, whereas
   * the elements of the trees are ordered with the largest on the right.
   *)

  (* functions for_sml walking the tree while keeping a stack of parents
   * to be visited.
   *)

  let rec next = function
    | [] -> (Empty, [])
    | (Red (x, a, b) as t) :: rest -> (t, left (b, rest))
    | (Black (x, a, b) as t) :: rest -> (t, left (b, rest))
    | Empty :: rest -> next rest

  and left = function
    | Empty, rest -> rest
    | (Red (x, a, b) as t), rest -> left (a, t :: rest)
    | (Black (x, a, b) as t), rest -> left (a, t :: rest)

  let rec start m = left (m, [])

  type 'a digit =
    | ZERO
    | ONE of ('a entry * 'a dict * 'a digit)
    | TWO of ('a entry * 'a dict * 'a entry * 'a dict * 'a digit)
  (* add an item that is guaranteed to be larger than any in l *)

  let rec addItem (a, l) =
    let rec incr = function
      | a, t, ZERO -> ONE (a, t, ZERO)
      | a1, t1, ONE (a2, t2, r) -> TWO (a1, t1, a2, t2, r)
      | a1, t1, TWO (a2, t2, a3, t3, r) ->
          ONE (a1, t1, incr (a2, Black (a3, t3, t2), r))
    in
    incr (a, Empty, l)
  (* link the digits into a tree *)

  let rec linkAll t =
    let rec link = function
      | t, ZERO -> t
      | t1, ONE (a, t2, r) -> link (Black (a, t2, t1), r)
      | t, TWO (a1, t1, a2, t2, r) -> link (Black (a1, Red (a2, t2, t1), t), r)
    in
    link (Empty, t)

  let rec getEntry = function Red (x, _, _) -> x | Black (x, _, _) -> x
  (* return the union of the two sets *)

  let rec union (Set (n1, s1), Set (n2, s2)) =
    let rec ins = function
      | (Empty, _), n, result -> (n, result)
      | (Red (x, _, _), r), n, result -> ins (next r, n + 1, addItem (x, result))
      | (Black (x, _, _), r), n, result ->
          ins (next r, n + 1, addItem (x, result))
    in
    let rec union' (t1, t2, n, result) =
      match (next t1, next t2) with
      | (Empty, _), (Empty, _) -> (n, result)
      | (Empty, _), t2 -> ins (t2, n, result)
      | t1, (Empty, _) -> ins (t1, n, result)
      | (tree1, r1), (tree2, r2) -> (
          let ((x, _) as e1) = getEntry tree1 in
          let ((y, _) as e2) = getEntry tree2 in
          match compare (x, y) with
          | Less -> union' (r1, t2, n + 1, addItem (e1, result))
          | Equal -> union' (r1, r2, n + 1, addItem (e1, result))
          | Greater -> union' (t1, r2, n + 1, addItem (e2, result)))
    in
    match s1 with
    | Empty -> Set (n2, s2)
    | _ -> (
        match s2 with
        | Empty -> Set (n1, s1)
        | _ ->
            let n, result = union' (start s1, start s2, 0, ZERO) in
            Set (n, linkAll result))
  (* return the intersection of the two sets *)

  let rec intersection (Set (_, s1), Set (_, s2)) =
    let rec intersect (t1, t2, n, result) =
      match (next t1, next t2) with
      | (Empty, r), (tree, r') -> (n, result)
      | (tree, r), (Empty, r') -> (n, result)
      | (tree1, r1), (tree2, r2) -> (
          let ((x, _) as e1) = getEntry tree1 in
          let ((y, _) as _e2) = getEntry tree2 in
          match compare (x, y) with
          | Less -> intersect (r1, t2, n, result)
          | Equal -> intersect (r1, r2, n + 1, addItem (e1, result))
          | Greater -> intersect (t1, r2, n, result))
    in
    let n, result = intersect (start s1, start s2, 0, ZERO) in
    Set (n, linkAll result)
  (* return the set difference  S1 - S2 
     if there are elements in S2 which do not appear in S1
     they are ignored !*)

  let rec difference (Set (_, s1), Set (_, s2)) =
    let rec ins = function
      | (Empty, _), n, result -> (n, result)
      | (Red (x, _, _), r), n, result -> ins (next r, n + 1, addItem (x, result))
      | (Black (x, _, _), r), n, result ->
          ins (next r, n + 1, addItem (x, result))
    in
    let rec diff (t1, t2, n, result) =
      match (next t1, next t2) with
      | (Empty, _), _ -> (n, result)
      | t1, (Empty, _) -> ins (t1, n, result)
      | (tree1, r1), (tree2, r2) -> (
          let ((x, _) as e1) = getEntry tree1 in
          let ((y, _) as _e2) = getEntry tree2 in
          match compare (x, y) with
          | Less -> diff (r1, t2, n + 1, addItem (e1, result))
          | Equal -> diff (r1, r2, n, result)
          | Greater -> diff (t1, r2, n, result))
    in
    let n, result = diff (start s1, start s2, 0, ZERO) in
    Set (n, linkAll result)
  (* returns difference (d1, d2) where d1 
     contains all elements occurring in S1 but not in S2
     and d2 contains all elements occurring in S2 but not in S1
       *)

  let rec difference2 (Set (_, s1), Set (_, s2)) =
    let rec ins = function
      | (Empty, _), n, result -> (n, result)
      | (Red (x, _, _), r), n, result -> ins (next r, n + 1, addItem (x, result))
      | (Black (x, _, _), r), n, result ->
          ins (next r, n + 1, addItem (x, result))
    in
    let rec diff (t1, t2, (n1, result1), (n2, result2)) =
      match (next t1, next t2) with
      | (Empty, _), t2 -> ((n1, result1), ins (t2, n2, result2))
      | t1, (Empty, _) -> (ins (t1, n1, result1), (n2, result2))
      | (tree1, r1), (tree2, r2) -> (
          let ((x, _) as e1) = getEntry tree1 in
          let ((y, _) as e2) = getEntry tree2 in
          match compare (x, y) with
          | Less -> diff (r1, t2, (n1 + 1, addItem (e1, result1)), (n2, result2))
          | Equal -> diff (r1, r2, (n1, result1), (n2, result2))
          | Greater ->
              diff (t1, r2, (n1, result1), (n2 + 1, addItem (e2, result2))))
    in
    let (n1, result1), (n2, result2) =
      diff (start s1, start s2, (0, ZERO), (0, ZERO))
    in
    (Set (n1, linkAll result1), Set (n2, linkAll result2))
  (* S1 - S2 = R1 
      S2 - S1 = R2
      intersection (S1, S2) requires 
      for_sml all (x, d1) in S1 
        and (x, d2) in S2, d1 ~ d2
    *)

  let rec diffMod f (Set (_, s1), Set (_, s2)) =
    let rec ins = function
      | (Empty, _), n, result -> (n, result)
      | (Red (x, _, _), r), n, result -> ins (next r, n + 1, addItem (x, result))
      | (Black (x, _, _), r), n, result ->
          ins (next r, n + 1, addItem (x, result))
    in
    let rec diff (t1, t2, (n1, result1), (n2, result2)) =
      match (next t1, next t2) with
      | (Empty, _), t2 -> ((n1, result1), ins (t2, n2, result2))
      | t1, (Empty, _) -> (ins (t1, n1, result1), (n2, result2))
      | (tree1, r1), (tree2, r2) -> (
          let ((x, d1) as e1) = getEntry tree1 in
          let ((y, d2) as e2) = getEntry tree2 in
          match compare (x, y) with
          | Less -> diff (r1, t2, (n1 + 1, addItem (e1, result1)), (n2, result2))
          | Equal ->
              f d1 d2;
              diff (r1, r2, (n1, result1), (n2, result2))
          | Greater ->
              diff (t1, r2, (n1, result1), (n2 + 1, addItem (e2, result2))))
    in
    let (n1, result1), (n2, result2) =
      diff (start s1, start s2, (0, ZERO), (0, ZERO))
    in
    (Set (n1, linkAll result1), Set (n2, linkAll result2))

  let rec splitSets f (Set (_, s1), Set (_, s2)) =
    let rec ins = function
      | (Empty, _), n, result -> (n, result)
      | (Red (x, _, _), r), n, result -> ins (next r, n + 1, addItem (x, result))
      | (Black (x, _, _), r), n, result ->
          ins (next r, n + 1, addItem (x, result))
    in
    let rec split (t1, t2, (n, result), (n1, result1), (n2, result2)) =
      match (next t1, next t2) with
      | (Empty, _), t2 -> ((n, result), (n1, result1), ins (t2, n2, result2))
      | t1, (Empty, _) -> ((n, result), ins (t1, n1, result1), (n2, result2))
      | (tree1, r1), (tree2, r2) -> (
          let ((x, d1) as e1) = getEntry tree1 in
          let ((y, d2) as e2) = getEntry tree2 in
          match compare (x, y) with
          | Less ->
              split
                ( r1,
                  t2,
                  (n, result),
                  (n1 + 1, addItem (e1, result1)),
                  (n2, result2) )
          | Equal -> (
              match f d1 d2 with
              | None ->
                  split
                    ( r1,
                      r2,
                      (n, result),
                      (n1 + 1, addItem (e1, result1)),
                      (n2 + 1, addItem (e2, result2)) )
              | Some d ->
                  split
                    ( r1,
                      r2,
                      (n + 1, addItem ((x, d), result)),
                      (n1, result1),
                      (n2, result2) ))
          | Greater ->
              split
                ( t1,
                  r2,
                  (n, result),
                  (n1, result1),
                  (n2 + 1, addItem (e2, result2)) ))
    in
    let (n, r), (n1, r1), (n2, r2) =
      split (start s1, start s2, (0, ZERO), (0, ZERO), (0, ZERO))
    in
    (Set (n, linkAll r), Set (n1, linkAll r1), Set (n2, linkAll r2))

  let rec new_ () = ref empty
  (* ignore size hint *)

  let rec copy s =
    let s' = new_ () in
    s' := !s;
    s'

  let insert = fun set -> fun entry -> set := insert (!set, entry)
  let insertLast = fun set -> fun datum -> set := insertLast (!set, datum)
  let insertList = fun set -> fun list -> set := insertList (!set, list)
  let insertShadow = fun set -> fun entry -> set := insertShadow (!set, entry)
  let isEmpty = fun ordSet -> isEmpty !ordSet
  let last = fun ordSet -> last !ordSet
  let lookup = fun ordSet -> fun key -> lookup !ordSet key
  let clear = fun ordSet -> ordSet := empty
  let app = fun ordSet -> fun f -> app f !ordSet

  let update =
   fun ordSet ->
    fun f ->
     ordSet := update f !ordSet;
     ordSet

  let forall = fun ordSet -> fun f -> forall !ordSet f
  let exists = fun ordSet -> fun f -> exists !ordSet f
  let existsOpt = fun ordSet -> fun f -> existsOpt !ordSet f
  let rec size s = setsize !s

  let difference =
   fun set1 ->
    fun set2 ->
     let set = new_ () in
     set := difference (!set1, !set2);
     set

  let difference2 =
   fun set1 ->
    fun set2 ->
     let r1 = new_ () in
     let r2 = new_ () in
     let rset1, rset2 = difference2 (!set1, !set2) in
     r1 := rset1;
     r2 := rset2;
     (r1, r2)

  let differenceModulo =
   fun set1 ->
    fun set2 ->
     fun f ->
      let r1 = new_ () in
      let r2 = new_ () in
      let rset1, rset2 = diffMod f (!set1, !set2) in
      r1 := rset1;
      r2 := rset2;
      (r1, r2)

  let splitSets =
   fun set1 ->
    fun set2 ->
     fun f ->
      let r1 = new_ () in
      let r2 = new_ () in
      let r = new_ () in
      let rset, rset1, rset2 = splitSets f (!set1, !set2) in
      r := rset;
      r1 := rset1;
      r2 := rset2;
      (r, r1, r2)

  let intersection =
   fun set1 ->
    fun set2 ->
     let set = new_ () in
     set := intersection (!set1, !set2);
     set

  let union =
   fun set1 ->
    fun set2 ->
     let set = new_ () in
     set := union (!set1, !set2);
     set
end

(* functor RedBlackSet *)
