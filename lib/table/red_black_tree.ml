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
    Empty                               (* considered black *)
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
         Red(e, Black lt, Black rt) (* GEN END FUN FIRST *)     (* re-color *)
    | (* GEN BEGIN FUN BRANCH *) restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt) (* GEN END FUN BRANCH *)     (* re-color *)
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
         Red(e, Black lt, Black rt) (* GEN END FUN FIRST *)     (* re-color *)
    | (* GEN BEGIN FUN BRANCH *) restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
         Red(e, Black lt, Black rt) (* GEN END FUN BRANCH *)     (* re-color *)
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

  (* function below from .../smlnj-lib/Util/int-redblack-set.sml *)
  (* Need to check and improve some time *)
  (* Sun Mar 13 08:22:53 2005 -fp *)

  (* Remove an item.  Returns true if old item found, false otherwise *)
    local
      exception NotFound
      datatype 'a zipper
        = TOP
        | LEFTB of ('a entry * 'a dict * 'a zipper)
        | LEFTR of ('a entry * 'a dict * 'a zipper)
        | RIGHTB of ('a dict * 'a entry * 'a zipper)
        | RIGHTR of ('a dict * 'a entry * 'a zipper)
    in
    fun delete t key =
        let
          fun (* GEN BEGIN FUN FIRST *) zip (TOP, t) = t (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) zip (LEFTB(x, b, z), a) = zip(z, Black(x, a, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) zip (LEFTR(x, b, z), a) = zip(z, Red(x, a, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) zip (RIGHTB(a, x, z), b) = zip(z, Black(x, a, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) zip (RIGHTR(a, x, z), b) = zip(z, Red(x, a, b)) (* GEN END FUN BRANCH *)
        (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *)
          fun (* GEN BEGIN FUN FIRST *) bbZip (TOP, t) = (true, t) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTB(x, Red(y, c, d), z), a) = (* case 1L *)
                bbZip (LEFTR(x, c, LEFTB(y, d, z)), a) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTB(x, Black(w, Red(y, c, d), e), z), a) = (* case 3L *)
                bbZip (LEFTB(x, Black(y, c, Red(w, d, e)), z), a) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTR(x, Black(w, Red(y, c, d), e), z), a) = (* case 3L *)
                bbZip (LEFTR(x, Black(y, c, Red(w, d, e)), z), a) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTB(x, Black(y, c, Red(w, d, e)), z), a) = (* case 4L *)
                (false, zip (z, Black(y, Black(x, a, c), Black(w, d, e)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTR(x, Black(y, c, Red(w, d, e)), z), a) = (* case 4L *)
                (false, zip (z, Red(y, Black(x, a, c), Black(w, d, e)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTR(x, Black(y, c, d), z), a) = (* case 2L *)
                (false, zip (z, Black(x, a, Red(y, c, d)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LEFTB(x, Black(y, c, d), z), a) = (* case 2L *)
                bbZip (z, Black(x, a, Red(y, c, d))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTB(Red(y, c, d), x, z), b) = (* case 1R *)
                bbZip (RIGHTR(d, x, RIGHTB(c, y, z)), b) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTR(Red(y, c, d), x, z), b) = (* case 1R *)
                bbZip (RIGHTR(d, x, RIGHTB(c, y, z)), b) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTB(Black(y, Red(w, c, d), e), x, z), b) = (* case 3R *)
                bbZip (RIGHTB(Black(w, c, Red(y, d, e)), x, z), b) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTR(Black(y, Red(w, c, d), e), x, z), b) = (* case 3R *)
                bbZip (RIGHTR(Black(w, c, Red(y, d, e)), x, z), b) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTB(Black(y, c, Red(w, d, e)), x, z), b) = (* case 4R *)
                (false, zip (z, Black(y, c, Black(x, Red(w, d, e), b)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTR(Black(y, c, Red(w, d, e)), x, z), b) = (* case 4R *)
                (false, zip (z, Red(y, c, Black(w, Red(w, d, e), b)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTR(Black(y, c, d), x, z), b) = (* case 2R *)
                (false, zip (z, Black(x, Red(y, c, d), b))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RIGHTB(Black(y, c, d), x, z), b) = (* case 2R *)
                bbZip (z, Black(x, Red(y, c, d), b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (z, t) = (false, zip(z, t)) (* GEN END FUN BRANCH *)
          fun (* GEN BEGIN FUN FIRST *) delMin (Red(y, Empty, b), z) = (y, (false, zip(z, b))) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Black(y, Empty, b), z) = (y, bbZip(z, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Black(y, a, b), z) = delMin(a, LEFTB(y, b, z)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Red(y, a, b), z) = delMin(a, LEFTR(y, b, z)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Empty, _) = raise Match (* GEN END FUN BRANCH *)
          fun (* GEN BEGIN FUN FIRST *) joinRed (Empty, Empty, z) = zip(z, Empty) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) joinRed (a, b, z) = let
                (* GEN BEGIN TAG OUTSIDE LET *) val (x, (needB, b')) = delMin(b, TOP) (* GEN END TAG OUTSIDE LET *)
                in
                  if needB
                    then #2(bbZip(z, Red(x, a, b')))
                    else zip(z, Red(x, a, b'))
                end (* GEN END FUN BRANCH *)
          fun (* GEN BEGIN FUN FIRST *) joinBlack (a, Empty, z) = #2(bbZip(z, a)) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) joinBlack (Empty, b, z) = #2(bbZip(z, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) joinBlack (a, b, z) = let
                (* GEN BEGIN TAG OUTSIDE LET *) val (x, (needB, b')) = delMin(b, TOP) (* GEN END TAG OUTSIDE LET *)
                in
                  if needB
                    then #2(bbZip(z, Black(x, a, b')))
                    else zip(z, Black(x, a, b'))
                end (* GEN END FUN BRANCH *)
          fun (* GEN BEGIN FUN FIRST *) del (Empty, z) = raise NotFound (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) del (Black(entry1 as (key1, datum1), a, b), z) =
              (case compare(key,key1)
                 of EQUAL => joinBlack (a, b, z)
                  | LESS => del (a, LEFTB(entry1, b, z))
                  | GREATER => del (b, RIGHTB(a, entry1, z))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) del (Red(entry1 as (key1, datum1), a, b), z) =
              (case compare(key,key1)
                 of EQUAL => joinRed (a, b, z)
                  | LESS => del (a, LEFTR(entry1, b, z))
                  | GREATER => del (b, RIGHTR(a, entry1, z))) (* GEN END FUN BRANCH *)
          in
            (del(t, TOP); true) handle NotFound => false
          end
    end (* local *)

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
    (* GEN BEGIN TAG OUTSIDE LET *) val delete = ((* GEN BEGIN FUNCTION EXPRESSION *) fn table => (* GEN BEGIN FUNCTION EXPRESSION *) fn key => (delete (!table) key; ()) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val clear = ((* GEN BEGIN FUNCTION EXPRESSION *) fn table => (table := Empty) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val app = ((* GEN BEGIN FUNCTION EXPRESSION *) fn f => (* GEN BEGIN FUNCTION EXPRESSION *) fn table => app f (!table) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
  end

end (* GEN END FUNCTOR DECL *);  (* functor RedBlackTree *)
