RedBlackTree  Key'   compare Key' * Key' -> Order    TABLE   Key Key'  struct type Keytype Entrytype Dicttype Table(* Representation Invariants *)
(*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)
let rec lookupdictkey let let rec lk(empty) nONE lk(red tree) lk' tree lk(black tree) lk' tree lk'((key1,  , datum1),  , left,  , right) (match compare (key,  , key1) with eQUAL -> sOME (datum1) lESS -> lk left gREATER -> lk right) in lk dict(* val restore_right : 'a dict -> 'a dict *)
(*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
let rec restore_right(black (e,  , red lt,  , red (rt as (_,  , red _,  , _)))) red (e,  , black lt,  , black rt) restore_right(black (e,  , red lt,  , red (rt as (_,  , _,  , red _)))) red (e,  , black lt,  , black rt) restore_right(black (e,  , l,  , red (re,  , red (rle,  , rll,  , rlr),  , rr))) black (rle,  , red (e,  , l,  , rll),  , red (re,  , rlr,  , rr)) restore_right(black (e,  , l,  , red (re,  , rl,  , rr as red _))) black (re,  , red (e,  , l,  , rl),  , rr) restore_rightdict dict(* restore_left is like restore_right, except *)
(* the color invariant may be violated only at the root of left child *)
let rec restore_left(black (e,  , red (lt as (_,  , red _,  , _)),  , red rt)) red (e,  , black lt,  , black rt) restore_left(black (e,  , red (lt as (_,  , _,  , red _)),  , red rt)) red (e,  , black lt,  , black rt) restore_left(black (e,  , red (le,  , ll as red _,  , lr),  , r)) black (le,  , ll,  , red (e,  , lr,  , r)) restore_left(black (e,  , red (le,  , ll,  , red (lre,  , lrl,  , lrr)),  , r)) black (lre,  , red (le,  , ll,  , lrl),  , red (e,  , lrr,  , r)) restore_leftdict dictlet rec insert(dict,  , entry as (key,  , datum)) let (* val ins : 'a dict -> 'a dict  inserts entry *)
(* ins (Red _) may violate color invariant at root *)
(* ins (Black _) or ins (Empty) will be red/black tree *)
(* ins preserves black height *)
let rec ins(empty) red (entry,  , empty,  , empty) ins(red (entry1 as (key1,  , datum1),  , left,  , right)) (match compare (key,  , key1) with eQUAL -> red (entry,  , left,  , right) lESS -> red (entry1,  , ins left,  , right) gREATER -> red (entry1,  , left,  , ins right)) ins(black (entry1 as (key1,  , datum1),  , left,  , right)) (match compare (key,  , key1) with eQUAL -> black (entry,  , left,  , right) lESS -> restore_left (black (entry1,  , ins left,  , right)) gREATER -> restore_right (black (entry1,  , left,  , ins right))) in match ins dict with red (t as (_,  , red _,  , _)) -> black t(* re-color *)
 red (t as (_,  , _,  , red _)) -> black t(* re-color *)
 dict -> dict(* use non-imperative version? *)
let rec insertShadow(dict,  , entry as (key,  , datum)) let let  in(* : 'a entry option ref *)
let rec ins(empty) red (entry,  , empty,  , empty) ins(red (entry1 as (key1,  , datum1),  , left,  , right)) (match compare (key,  , key1) with eQUAL -> (oldEntry := sOME (entry1); red (entry,  , left,  , right)) lESS -> red (entry1,  , ins left,  , right) gREATER -> red (entry1,  , left,  , ins right)) ins(black (entry1 as (key1,  , datum1),  , left,  , right)) (match compare (key,  , key1) with eQUAL -> (oldEntry := sOME (entry1); black (entry,  , left,  , right)) lESS -> restore_left (black (entry1,  , ins left,  , right)) gREATER -> restore_right (black (entry1,  , left,  , ins right))) in (oldEntry := nONE; ((match ins dict with red (t as (_,  , red _,  , _)) -> black t(* re-color *)
 red (t as (_,  , _,  , red _)) -> black t(* re-color *)
 dict -> dict),  , ! oldEntry))let rec appfdict let let rec ap(empty) () ap(red tree) ap' tree ap(black tree) ap' tree ap'(entry1,  , left,  , right) (ap left; f entry1; ap right) in ap dictlet rec new(n) ref (empty)(* ignore size hint *)
let  inlet  inlet  inlet  inlet  inend   module module