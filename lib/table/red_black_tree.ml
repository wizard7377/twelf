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
    Empty                               (* considered black *)
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
         Red(e, Black lt, Black rt)     (* re-color *)
    | (Black(e, Red lt, Red (rt as (_,_,Red _)))) -> 
         Red(e, Black lt, Black rt)     (* re-color *)
    | (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) -> 
         (* l is black, deep rotate *)
         Black(rle, Red(e, l, rll), Red(re, rlr, rr))
    | (Black(e, l, Red(re, rl, rr as Red _))) -> 
         (* l is black, shallow rotate *)
         Black(re, Red(e, l, rl), rr)
    | dict -> dict

  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  let rec restore_left = function (Black(e, Red (lt as (_,Red _,_)), Red rt)) -> 
         Red(e, Black lt, Black rt)     (* re-color *)
    | (Black(e, Red (lt as (_,_,Red _)), Red rt)) -> 
         Red(e, Black lt, Black rt)     (* re-color *)
    | (Black(e, Red(le, ll as Red _, lr), r)) -> 
         (* r is black, shallow rotate *)
         Black(le, ll, Red(e, lr, r))
    | (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) -> 
         (* r is black, deep rotate *)
         Black(lre, Red(le, ll, lrl), Red(e, lrr, r))
    | dict -> dict

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
        | (Black(entry1 as (key1, datum1), left, right)) -> 
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

  (* function below from .../smlnj-lib/Util/int-redblack-set.sml *)
  (* Need to check and improve some time *)
  (* Sun Mar 13 08:22:53 2005 -fp *)

  (* Remove an item.  Returns true if old item found, false otherwise *)
    local
      exception NotFound
      type 'a zipper
        = TOP
        | LEFTB of ('a entry * 'a dict * 'a zipper)
        | LEFTR of ('a entry * 'a dict * 'a zipper)
        | RIGHTB of ('a dict * 'a entry * 'a zipper)
        | RIGHTR of ('a dict * 'a entry * 'a zipper)
    in
    fun delete t key =
        let
          let rec zip = function (TOP, t) -> t
            | (LEFTB(x, b, z), a) -> zip(z, Black(x, a, b))
            | (LEFTR(x, b, z), a) -> zip(z, Red(x, a, b))
            | (RIGHTB(a, x, z), b) -> zip(z, Black(x, a, b))
            | (RIGHTR(a, x, z), b) -> zip(z, Red(x, a, b))
        (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *)
          let rec bbZip = function (TOP, t) -> (true, t)
            | (LEFTB(x, Red(y, c, d), z), a) -> (* case 1L *)
                bbZip (LEFTR(x, c, LEFTB(y, d, z)), a)
            | (LEFTB(x, Black(w, Red(y, c, d), e), z), a) -> (* case 3L *)
                bbZip (LEFTB(x, Black(y, c, Red(w, d, e)), z), a)
            | (LEFTR(x, Black(w, Red(y, c, d), e), z), a) -> (* case 3L *)
                bbZip (LEFTR(x, Black(y, c, Red(w, d, e)), z), a)
            | (LEFTB(x, Black(y, c, Red(w, d, e)), z), a) -> (* case 4L *)
                (false, zip (z, Black(y, Black(x, a, c), Black(w, d, e))))
            | (LEFTR(x, Black(y, c, Red(w, d, e)), z), a) -> (* case 4L *)
                (false, zip (z, Red(y, Black(x, a, c), Black(w, d, e))))
            | (LEFTR(x, Black(y, c, d), z), a) -> (* case 2L *)
                (false, zip (z, Black(x, a, Red(y, c, d))))
            | (LEFTB(x, Black(y, c, d), z), a) -> (* case 2L *)
                bbZip (z, Black(x, a, Red(y, c, d)))
            | (RIGHTB(Red(y, c, d), x, z), b) -> (* case 1R *)
                bbZip (RIGHTR(d, x, RIGHTB(c, y, z)), b)
            | (RIGHTR(Red(y, c, d), x, z), b) -> (* case 1R *)
                bbZip (RIGHTR(d, x, RIGHTB(c, y, z)), b)
            | (RIGHTB(Black(y, Red(w, c, d), e), x, z), b) -> (* case 3R *)
                bbZip (RIGHTB(Black(w, c, Red(y, d, e)), x, z), b)
            | (RIGHTR(Black(y, Red(w, c, d), e), x, z), b) -> (* case 3R *)
                bbZip (RIGHTR(Black(w, c, Red(y, d, e)), x, z), b)
            | (RIGHTB(Black(y, c, Red(w, d, e)), x, z), b) -> (* case 4R *)
                (false, zip (z, Black(y, c, Black(x, Red(w, d, e), b))))
            | (RIGHTR(Black(y, c, Red(w, d, e)), x, z), b) -> (* case 4R *)
                (false, zip (z, Red(y, c, Black(w, Red(w, d, e), b))))
            | (RIGHTR(Black(y, c, d), x, z), b) -> (* case 2R *)
                (false, zip (z, Black(x, Red(y, c, d), b)))
            | (RIGHTB(Black(y, c, d), x, z), b) -> (* case 2R *)
                bbZip (z, Black(x, Red(y, c, d), b))
            | (z, t) -> (false, zip(z, t))
          let rec delMin = function (Red(y, Empty, b), z) -> (y, (false, zip(z, b)))
            | (Black(y, Empty, b), z) -> (y, bbZip(z, b))
            | (Black(y, a, b), z) -> delMin(a, LEFTB(y, b, z))
            | (Red(y, a, b), z) -> delMin(a, LEFTR(y, b, z))
            | (Empty, _) -> raise Match
          let rec joinRed = function (Empty, Empty, z) -> zip(z, Empty)
            | (a, b, z) -> let
                let (x, (needB, b')) = delMin(b, TOP)
                in
                  if needB
                    then #2(bbZip(z, Red(x, a, b')))
                    else zip(z, Red(x, a, b'))
                end
          let rec joinBlack = function (a, Empty, z) -> #2(bbZip(z, a))
            | (Empty, b, z) -> #2(bbZip(z, b))
            | (a, b, z) -> let
                let (x, (needB, b')) = delMin(b, TOP)
                in
                  if needB
                    then #2(bbZip(z, Black(x, a, b')))
                    else zip(z, Black(x, a, b'))
                end
          let rec del = function (Empty, z) -> raise NotFound
            | (Black(entry1 as (key1, datum1), a, b), z) -> 
              (case compare(key,key1)
                 of EQUAL => joinBlack (a, b, z)
                  | LESS => del (a, LEFTB(entry1, b, z))
                  | GREATER => del (b, RIGHTB(a, entry1, z)))
            | (Red(entry1 as (key1, datum1), a, b), z) -> 
              (case compare(key,key1)
                 of EQUAL => joinRed (a, b, z)
                  | LESS => del (a, LEFTR(entry1, b, z))
                  | GREATER => del (b, RIGHTR(a, entry1, z)))
          in
            (del(t, TOP); true) handle NotFound => false
          end
    end (* local *)

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
            | (Black(entry1 as (key1, datum1), left, right)) -> 
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
    let delete = (fun table -> fun key -> (delete (!table) key; ()))
    let clear = (fun table -> (table := Empty))
    let app = (fun f -> fun table -> app f (!table))
  end

end;; (* functor RedBlackTree *)
