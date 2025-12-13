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
 * its child will be a red leaf.
 *)
structure RBSet : RBSET = 

struct

  type key = int
  type 'a entry = key * 'a

 datatype 'a dict =
    Empty				(* considered black *)
  | Red of 'a entry * 'a dict * 'a dict
  | Black of 'a entry * 'a dict * 'a dict

  datatype 'a set = Set of (int * 'a dict)

  exception Error of string

  type 'a ord_set = 'a set ref

  fun (* GEN BEGIN FUN FIRST *) isEmpty (Set(_, Empty)) = true (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) isEmpty (Set(_,T)) = false (* GEN END FUN BRANCH *)

  (* GEN BEGIN TAG OUTSIDE LET *) val empty = Set(0, Empty) (* GEN END TAG OUTSIDE LET *)
  
  fun singleton x = Set(1, Red(x, Empty, Empty))

  (* GEN BEGIN TAG OUTSIDE LET *) val compare = Int.compare (* GEN END TAG OUTSIDE LET *)
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

  fun lookup (Set(n, dict)) key =
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


  fun last (Set(n, dict)) = (n, valOf (lookup (Set(n, dict)) n))

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
    | (* GEN BEGIN FUN BRANCH *) restore_right (Black(e, l, Red (re, rl, rr as Red _))) =
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

  fun insert (Set(n, dict), entry as (key, datum)) = 
    let      
      (* GEN BEGIN TAG OUTSIDE LET *) val nItems = ref n (* GEN END TAG OUTSIDE LET *)
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      fun (* GEN BEGIN FUN FIRST *) ins (Empty) = (nItems := n+1; Red(entry, Empty, Empty)) (* GEN END FUN FIRST *)
  	| (* GEN BEGIN FUN BRANCH *) ins (Red(entry1 as (key1, datum1), left, right)) =
  	  (case compare(key,key1)
  	     of EQUAL => 
              ((*print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n");*)
  	       Red(entry1, left, right))
  	      | LESS => Red(entry1, ins left, right)
  	      | GREATER => Red(entry1, left, ins right)) (* GEN END FUN BRANCH *)
  	| (* GEN BEGIN FUN BRANCH *) ins (Black(entry1 as (key1, datum1), left, right)) =
  	  (case compare(key,key1)
  	     of EQUAL => 
  	       ((* print ("Found " ^ Int.toString key ^ " already in set -- keep entry--do not overwrite\n"); *)
  		Black(entry1, left, right))
  	      | LESS => restore_left (Black(entry1, ins left, right))
  	      | GREATER => restore_right (Black(entry1, left, ins right))) (* GEN END FUN BRANCH *)
      (* GEN BEGIN TAG OUTSIDE LET *) val dict' =  case ins dict
        	            of Red (t as (_, Red _, _)) => Black t (* re-color *)
        		  | Red (t as (_, _, Red _)) => Black t (* re-color *)
        		  | dict => dict (* GEN END TAG OUTSIDE LET *)
    in
      Set(!nItems, dict')
    end


  fun (* GEN BEGIN FUN FIRST *) insertList (S, nil) = S (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) insertList (S, e::list) = insertList (insert (S, e), list) (* GEN END FUN BRANCH *)


  fun insertLast (Set(n, dict), datum) = 
    let
      (* GEN BEGIN TAG OUTSIDE LET *) val Set(n', dic') =  insert (Set(n, dict), (n+1, datum)) (* GEN END TAG OUTSIDE LET *)
    in 
      Set(n', dic')
    end 
  (* input: set sc
     output set s' *)


  fun insertShadow (Set(n, dict), entry as (key, datum)) =  
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
      (* GEN BEGIN TAG OUTSIDE LET *) val (dict', oldEntry') = (oldEntry := NONE;
        				((case ins dict
        				    of Red (t as (_, Red _, _)) => Black t (* re-color *)
        				  | Red (t as (_, _, Red _)) => Black t (* re-color *)
        				  | dict => dict),
        				    !oldEntry)) (* GEN END TAG OUTSIDE LET *)
    in
      Set(n, dict')
    end

  (* Remove an item.  Raises LibBase.NotFound if not found. *)
    local
      datatype color = RedColor | BlackColor

      datatype 'a zipper
        = Top
        | LeftRed of ('a entry * 'a dict * 'a zipper)
        | LeftBlack of ('a entry * 'a dict * 'a zipper)
        | RightRed of ('a dict * 'a entry * 'a zipper)
        | RightBlack of ('a dict * 'a entry * 'a zipper)
    in
    fun delete (Set(nItems, t), k) = 
        let
    	  fun (* GEN BEGIN FUN FIRST *) zip (Top, t) = t (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) zip (LeftRed(x, b, z), a) = zip(z, Red(x, a, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) zip (LeftBlack(x, b, z), a) = zip(z, Black(x, a, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) zip (RightRed(a, x, z), b) = zip(z, Red(x, a, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) zip (RightBlack(a, x, z), b) = zip(z, Black(x, a, b)) (* GEN END FUN BRANCH *)
    	  (* bbZip propagates a black deficit up the tree until either the top
         * is reached, or the deficit can be covered.  It returns a boolean
         * that is true if there is still a deficit and the zipped tree.
         *)
          fun (* GEN BEGIN FUN FIRST *) bbZip (Top, t) = (true, t) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftBlack(x, Red(y, c, d), z), a) = (* case 1L *)
                bbZip (LeftRed(x, c, LeftBlack(y, d, z)), a) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftRed(x, Red(y, c, d), z), a) = (* case 1L *)
                bbZip (LeftRed(x, c, LeftBlack(y, d, z)), a) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftBlack(x, Black(w, Red(y, c, d), e), z), a) = (* case 3L *)
                bbZip (LeftBlack(x, Black(y, c, Red(w, d, e)), z), a) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftRed(x, Black(w, Red(y, c, d), e), z), a) = (* case 3L *)
                bbZip (LeftRed(x, Black(y, c, Red(w, d, e)), z), a) (* GEN END FUN BRANCH *)
    
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftBlack(x, Black(y, c, Red(w, d, e)), z), a) = (* case 4L *)
                (false, zip (z, Black(y, Black(x, a, c), Black(w, d, e)))) (* GEN END FUN BRANCH *)
    
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftRed(x, Black(y, c, Red(w, d, e)), z), a) = (* case 4L *)
                (false, zip (z, Red(y, Black(x, a, c), Black(w, d, e)))) (* GEN END FUN BRANCH *)
    
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftRed(x, Black(y, c, d), z), a) = (* case 2L *)
                (false, zip (z, Black(x, a, Red(y, c, d)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (LeftBlack(x, Black(y, c, d), z), a) = (* case 2L *)
                bbZip (z, Black(x, a, Red(y, c, d))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RightBlack(Red(y, c, d), x, z), b) = (* case 1R *)
                bbZip (RightRed(d, x, RightBlack(c, y, z)), b) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RightRed(Red(y, c, d), x, z), b) = (* case 1R *)
                bbZip (RightRed(d, x, RightBlack(c, y, z)), b) (* GEN END FUN BRANCH *)
    	    | (* GEN BEGIN FUN BRANCH *) bbZip (RightBlack(Black(y , Red(w, c, d), e), x, z), b) = (* case 3R *)
                bbZip (RightBlack(Black(w, c, Red(y, d, e)), x, z), b) (* GEN END FUN BRANCH *)
    	    | (* GEN BEGIN FUN BRANCH *) bbZip (RightRed(Black(y , Red(w, c, d), e), x, z), b) = (* case 3R *)
                bbZip (RightRed(Black(w, c, Red(y, d, e)), x, z), b) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RightBlack(Black(y, c, Red(w, d, e)), x, z), b) = (* case 4R *)
                (false, zip (z, Black(y, c, Black(x, Red(w, d, e), b)))) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) bbZip (RightRed(Black(y, c, Red(w, d, e)), x, z), b) = (* case 4R *)
                (false, zip (z, Red(y, c, Black(x, Red(w, d, e), b)))) (* GEN END FUN BRANCH *)
    
            | (* GEN BEGIN FUN BRANCH *) bbZip (RightRed(Black(y, c, d), x, z), b) = (* case 2R *)
                (false, zip (z, Black(x, Red(y, c,  d), b))) (* GEN END FUN BRANCH *)
    
            | (* GEN BEGIN FUN BRANCH *) bbZip (RightBlack(Black(y, c, d), x, z), b) = (* case 2R *)
                bbZip (z, Black(x, Red(y, c, d),  b)) (* GEN END FUN BRANCH *)
    
            | (* GEN BEGIN FUN BRANCH *) bbZip (z, t) = (false, zip(z, t)) (* GEN END FUN BRANCH *)
    
          fun (* GEN BEGIN FUN FIRST *) delMin (Red(y, Empty, b), z) = (y, (false, zip(z, b))) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Black(y , Empty, b), z) = (y, bbZip(z, b)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Red(y, a, b), z) = delMin(a, LeftRed(y, b, z)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) delMin (Black(y, a, b), z) = delMin(a, LeftBlack(y, b, z)) (* GEN END FUN BRANCH *)
    
    	  fun (* GEN BEGIN FUN FIRST *) joinBlack (a, Empty, z) = #2(bbZip(z, a)) (* GEN END FUN FIRST *)       
    	    | (* GEN BEGIN FUN BRANCH *) joinBlack (Empty, b, z) = #2(bbZip(z, b)) (* GEN END FUN BRANCH *)       
    	    | (* GEN BEGIN FUN BRANCH *) joinBlack (a, b, z) = let
                (* GEN BEGIN TAG OUTSIDE LET *) val (x, (needB, b')) = delMin(b, Top) (* GEN END TAG OUTSIDE LET *)
                in
                  if needB
                    then #2(bbZip(z, Black(x, a, b')))
                    else zip(z, Black(x, a, b'))
                end (* GEN END FUN BRANCH *)
    
    	  fun (* GEN BEGIN FUN FIRST *) joinRed (Empty, Empty, z) = zip(z, Empty) (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) joinRed (a, b, z) = let
                (* GEN BEGIN TAG OUTSIDE LET *) val (x, (needB, b')) = delMin(b, Top) (* GEN END TAG OUTSIDE LET *)
                in
                  if needB
                    then #2(bbZip(z, Red(x, a, b')))
                    else zip(z, Red(x, a, b'))
                end (* GEN END FUN BRANCH *)
    
          fun (* GEN BEGIN FUN FIRST *) del (Empty, z) = raise Error "not found\n" (* GEN END FUN FIRST *)
            | (* GEN BEGIN FUN BRANCH *) del (Red(y as (k', _), a, b), z) = (case compare(k, k')
                 of LESS => del (a, LeftRed(y, b, z))
                  | EQUAL => joinRed (a, b, z)
                  | GREATER => del (b, RightRed(a, y, z))
                (* end case *)) (* GEN END FUN BRANCH *)
            | (* GEN BEGIN FUN BRANCH *) del (Black(y as (k', _), a, b), z) = (case compare(k, k')
                 of LESS => del (a, LeftBlack(y, b, z))
                  | EQUAL => joinBlack (a, b, z)
                  | GREATER => del (b, RightBlack(a, y, z))
                (* end case *)) (* GEN END FUN BRANCH *)
          in
            Set(nItems-1, del(t, Top))
          end
    end (* local *)


  (* does not apply f to all elements of S in order! *)
  fun app f (Set(n, dict)) =
      let fun (* GEN BEGIN FUN FIRST *) ap (Empty) = () (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Red tree) = ap' tree (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Black tree) = ap' tree (* GEN END FUN BRANCH *)
  	  and ap' (entry1 as (_, datum), left, right) =
  	      (ap left; f datum; ap right)
      in
  	ap dict
      end

  fun update f (Set(n, dict)) =
      let fun (* GEN BEGIN FUN FIRST *) upd (Empty) = Empty (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) upd (Red tree) = Red(upd' tree) (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) upd (Black tree) = Black(upd' tree) (* GEN END FUN BRANCH *)
  	  and upd' (entry1 as (k, datum), left, right) =
  	      let
  		 (* GEN BEGIN TAG OUTSIDE LET *) val left' = upd left (* GEN END TAG OUTSIDE LET *)
  		 (* GEN BEGIN TAG OUTSIDE LET *) val datum' = f datum (* GEN END TAG OUTSIDE LET *)
  		 (* GEN BEGIN TAG OUTSIDE LET *) val right' =  upd right (* GEN END TAG OUTSIDE LET *)
  	       in 
  		 ((k, datum'), left', right')
  	       end 
      in
  	Set(n, upd dict)
      end

  fun forall (Set(n, dict)) f =
      let fun (* GEN BEGIN FUN FIRST *) ap (Empty) = () (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Red tree) = ap' tree (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Black tree) = ap' tree (* GEN END FUN BRANCH *)
  	  and ap' (entry, left, right) =
  	      (ap left; f entry; ap right)
      in
  	ap dict
      end

  fun existsOpt (Set(n, dict)) f =
      let fun (* GEN BEGIN FUN FIRST *) ap (Empty) = NONE (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Red tree) = ap' tree (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Black tree) = ap' tree (* GEN END FUN BRANCH *)
  	  and ap' (entry as (k,d), left, right) =
  	      (if (f d) then (print "SUCCESS\n"; SOME(k))
  		 else  (print "FAILED\n"; (case (ap left) of NONE => ap right | SOME(res) => SOME(res))))
      in
  	ap dict
      end

  fun exists (Set(n, dict)) f =
      let fun (* GEN BEGIN FUN FIRST *) ap (Empty) = false (* GEN END FUN FIRST *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Red tree) = ap' tree (* GEN END FUN BRANCH *)
  	    | (* GEN BEGIN FUN BRANCH *) ap (Black tree) = ap' tree (* GEN END FUN BRANCH *)
  	  and ap' (entry, left, right) =
  	      if (f entry) 
  		then true
  	      else (if (ap left) then true else (ap right))
      in
  	ap dict
      end


  fun setsize (Set (n, _)) = n

  (* support for constructing red-black trees in linear time from increasing
   * ordered sequences (based on a description by R. Hinze).  Note that the
   * elements in the digits are ordered with the largest on the left, whereas
   * the elements of the trees are ordered with the largest on the right.
   *)
  (* functions for walking the tree while keeping a stack of parents
   * to be visited.
   *)
    fun (* GEN BEGIN FUN FIRST *) next ((t as Red( _, _, b))::rest) = (t, left(b, rest)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) next ((t as Black( _, _, b))::rest) = (t, left(b, rest)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) next _ = (Empty, []) (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) left (Empty, rest) = rest (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) left (t as Red(_, a, _), rest) = left(a, t::rest) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) left (t as Black(_, a, _), rest) = left(a, t::rest) (* GEN END FUN BRANCH *)
    fun start m = left(m, [])

    datatype 'a digit
      = ZERO
      | ONE of ('a entry * 'a dict * 'a digit)
      | TWO of ('a entry * 'a dict * 'a entry * 'a dict * 'a digit)
  (* add an item that is guaranteed to be larger than any in l *)
    fun addItem (a, l) = 
      let
    	fun (* GEN BEGIN FUN FIRST *) incr (a, t, ZERO) = ONE(a, t, ZERO) (* GEN END FUN FIRST *)
    	  | (* GEN BEGIN FUN BRANCH *) incr (a1, t1, ONE(a2, t2, r)) = TWO(a1, t1, a2, t2, r) (* GEN END FUN BRANCH *)
    	  | (* GEN BEGIN FUN BRANCH *) incr (a1, t1, TWO(a2, t2, a3, t3, r)) =
    	  ONE(a1, t1, incr(a2, Black (a3, t3, t2), r)) (* GEN END FUN BRANCH *)
      in
    	incr(a, Empty, l)
      end
  (* link the digits into a tree *)
    fun linkAll t = let
    	  fun (* GEN BEGIN FUN FIRST *) link (t, ZERO) = t (* GEN END FUN FIRST *)
    	    | (* GEN BEGIN FUN BRANCH *) link (t1, ONE(a, t2, r)) = link(Black (a, t2, t1), r) (* GEN END FUN BRANCH *)
    	    | (* GEN BEGIN FUN BRANCH *) link (t, TWO(a1, t1, a2, t2, r)) =
    		link(Black (a1, Red(a2, t2, t1),  t), r) (* GEN END FUN BRANCH *)
    	  in
    	    link (Empty, t)
    	  end

    fun (* GEN BEGIN FUN FIRST *) getEntry (Red (x, _, _)) = x (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) getEntry (Black (x, _, _)) = x (* GEN END FUN BRANCH *)

      
  (* return the union of the two sets *)
    fun union (Set (n1, s1), Set (n2, s2)) = 
      let
    	fun (* GEN BEGIN FUN FIRST *) ins ((Empty, _), n, result) = (n, result) (* GEN END FUN FIRST *)
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Red (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *)
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Black (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *)
    	  fun union' (t1, t2, n, result) = 
    	    (case (next t1, next t2)
    	       of ((Empty, _), (Empty, _)) => (n, result)
    	        | ((Empty, _), t2) => ins(t2, n, result)
    		| (t1, (Empty, _)) => ins(t1, n, result)
    		| ((tree1, r1), (tree2, r2))  => 
    		 let 
    		   (* GEN BEGIN TAG OUTSIDE LET *) val e1 as (x, d1) = getEntry tree1 (* GEN END TAG OUTSIDE LET *)
    		   (* GEN BEGIN TAG OUTSIDE LET *) val e2 as (y, d2) = getEntry tree2 (* GEN END TAG OUTSIDE LET *)
    		 in 
    		   case compare(x, y)
    		     of LESS => union' (r1, t2, n+1, addItem(e1, result))
    		      | EQUAL => union' (r1, r2, n+1, addItem(e1, result))
    		      | GREATER => union' (t1, r2, n+1, addItem(e2, result))
    		 end)
      in
    	case s1 of 
    	  Empty => Set(n2, s2)
    	| _ => (case s2 of 
    		  Empty => Set(n1, s1)
    		| _ => let
    			 (* GEN BEGIN TAG OUTSIDE LET *) val (n, result) = union' (start s1, start s2, 0, ZERO) (* GEN END TAG OUTSIDE LET *) 
    		       in 
    			 Set(n, linkAll result)
    		       end)
      end

  (* return the intersection of the two sets *)
    fun intersection (Set(_, s1), Set(_, s2)) = 
      let
    	fun intersect (t1, t2, n, result) = 
    	  (case (next t1, next t2)
    	     of ((Empty, r), (tree, r')) => (n, result)
    	       | ((tree, r), (Empty, r')) => (n, result)
    	       | ((tree1, r1), (tree2, r2)) => 
    	       let
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e1 as (x, d1) = getEntry tree1 (* GEN END TAG OUTSIDE LET *)
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e2 as (y, d2) = getEntry tree2 (* GEN END TAG OUTSIDE LET *)
    	       in 
    		 case compare(x, y)
    		   of LESS => intersect (r1, t2, n, result)
    		 | EQUAL => intersect (r1, r2, n+1, addItem(e1, result))
    		 | GREATER => intersect (t1, r2, n, result)
    	       end)
    	(* GEN BEGIN TAG OUTSIDE LET *) val (n, result) = intersect (start s1, start s2, 0, ZERO) (* GEN END TAG OUTSIDE LET *)
      in
    	Set(n, linkAll result)
      end


  (* return the set difference  S1 - S2 
     if there are elements in S2 which do not appear in S1
     they are ignored !*)
    fun difference (Set(_, s1), Set(_, s2)) = 
      let
    	fun (* GEN BEGIN FUN FIRST *) ins ((Empty, _), n, result) = (n, result) (* GEN END FUN FIRST *)
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Red (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Black (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	fun diff (t1, t2, n, result) = 
    	  (case (next t1, next t2)
    	     of ((Empty, _), _) => (n, result)
    	      | (t1, (Empty, _)) => ins(t1, n, result)
    	      | ((tree1, r1), (tree2, r2)) => 
    	       let
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e1 as (x, d1) = getEntry tree1 (* GEN END TAG OUTSIDE LET *)
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e2 as (y, d2) = getEntry tree2 (* GEN END TAG OUTSIDE LET *)
    	       in 
    		 case compare(x, y)
    		   of LESS => diff (r1, t2, n+1, addItem(e1, result))
    		    | EQUAL => diff (r1, r2, n, result)
    		    | GREATER => diff (t1, r2, n, result)
    	       end)
    	(* GEN BEGIN TAG OUTSIDE LET *) val (n, result) = diff (start s1, start s2, 0, ZERO) (* GEN END TAG OUTSIDE LET *)
      in
    	Set(n, linkAll result)
      end

    (* returns difference (d1, d2) where d1 
     contains all elements occurring in S1 but not in S2
     and d2 contains all elements occurring in S2 but not in S1
       *)
    fun difference2 (Set(_, s1), Set(_, s2)) = 
      let
    	fun (* GEN BEGIN FUN FIRST *) ins ((Empty, _), n, result) = (n, result) (* GEN END FUN FIRST *)
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Red (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Black (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	fun diff (t1, t2, (n1, result1), (n2, result2)) = 
    	  (case (next t1, next t2)
    	     of ((Empty, _), t2) => ((n1, result1), ins(t2, n2, result2))
    	      | (t1, (Empty, _)) => (ins(t1, n1, result1), (n2, result2))
    	      | ((tree1, r1), (tree2, r2)) => 
    	       let
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e1 as (x, d1) = getEntry tree1 (* GEN END TAG OUTSIDE LET *)
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e2 as (y, d2) = getEntry tree2 (* GEN END TAG OUTSIDE LET *)
    	       in 
    		 case compare(x, y)
    		   of LESS => diff (r1, t2, (n1+1, addItem(e1, result1)), (n2, result2))
    		    | EQUAL => diff (r1, r2, (n1, result1), (n2, result2))
    		    | GREATER => diff (t1, r2, (n1, result1), (n2+1, addItem(e2, result2)))
    	       end)
    	(* GEN BEGIN TAG OUTSIDE LET *) val ((n1, result1), (n2, result2)) = diff (start s1, start s2, (0, ZERO), (0, ZERO)) (* GEN END TAG OUTSIDE LET *)
      in
    	(Set(n1, linkAll result1), Set(n2, linkAll result2))
      end


   (* S1 - S2 = R1 
      S2 - S1 = R2
      intersection (S1, S2) requires 
      for all (x, d1) in S1 
        and (x, d2) in S2, d1 ~ d2
    *)

    fun diffMod F (Set(_, s1), Set(_, s2)) = 
     let
    	fun (* GEN BEGIN FUN FIRST *) ins ((Empty, _), n, result) = (n, result) (* GEN END FUN FIRST *)
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Red (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Black (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	fun diff (t1, t2, (n1, result1), (n2, result2)) = 
    	  (case (next t1, next t2)
    	     of ((Empty, _), t2) => ((n1, result1), ins(t2, n2, result2))
    	      | (t1, (Empty, _)) => (ins(t1, n1, result1), (n2, result2))
    	      | ((tree1, r1), (tree2, r2)) => 
    	       let
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e1 as (x, d1) = getEntry tree1 (* GEN END TAG OUTSIDE LET *)
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e2 as (y, d2) = getEntry tree2 (* GEN END TAG OUTSIDE LET *)
    	       in 
    		 case compare(x, y)
    		   of LESS => diff (r1, t2, (n1+1, addItem(e1, result1)), (n2, result2))
    		    | EQUAL => ((F d1 d2) ; diff (r1, r2, (n1, result1), (n2, result2)))
    		    | GREATER => diff (t1, r2, (n1, result1), (n2+1, addItem(e2, result2)))
    	       end)
    	(* GEN BEGIN TAG OUTSIDE LET *) val ((n1, result1), (n2, result2)) = diff (start s1, start s2, (0, ZERO), (0, ZERO)) (* GEN END TAG OUTSIDE LET *)
      in
    	(Set(n1, linkAll result1), Set(n2, linkAll result2))
      end


    fun splitSets F (Set(_, s1), Set(_, s2)) = 
     let
    	fun (* GEN BEGIN FUN FIRST *) ins ((Empty, _), n, result) = (n, result) (* GEN END FUN FIRST *)
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Red (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	  | (* GEN BEGIN FUN BRANCH *) ins ((Black (x, _, _), r), n, result) =
    	    ins(next r, n+1, addItem(x, result)) (* GEN END FUN BRANCH *) 
    	fun split (t1, t2, nr as (n, result), nr1 as (n1, result1), nr2 as (n2, result2)) = 
    	  (case (next t1, next t2)
    	     of ((Empty, _), t2) => (nr, nr1, ins(t2, n2, result2))
    	      | (t1, (Empty, _)) => (nr, ins(t1, n1, result1), nr2)
    	      | ((tree1, r1), (tree2, r2)) => 
    	       let
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e1 as (x, d1) = getEntry tree1 (* GEN END TAG OUTSIDE LET *)
    		 (* GEN BEGIN TAG OUTSIDE LET *) val e2 as (y, d2) = getEntry tree2 (* GEN END TAG OUTSIDE LET *)
    	       in 
    		 case compare(x, y)
    		   of LESS => split (r1, t2, nr, (n1+1, addItem(e1, result1)), nr2)
    		    | EQUAL => (case (F d1 d2) 
    				  of NONE => split (r1, r2, nr, (n1+1, addItem(e1, result1)), 
    						   (n2+1, addItem(e2, result2)))
    		                   | SOME(d) => split (r1, r2, (n+1, addItem((x, d), result)), nr1, nr2))
    		    | GREATER => split (t1, r2, nr, nr1, (n2+1, addItem(e2, result2)))
    	       end)
    	(* GEN BEGIN TAG OUTSIDE LET *) val ((n, r), (n1, r1), (n2, r2)) = split (start s1, start s2, (0, ZERO), (0, ZERO), (0, ZERO)) (* GEN END TAG OUTSIDE LET *)
      in
    	(Set(n, linkAll r), Set(n1, linkAll r1), Set(n2, linkAll r2))
      end

  in
    fun new () = ref (empty) (* ignore size hint *)
    fun copy S = let (* GEN BEGIN TAG OUTSIDE LET *) val S' = new() (* GEN END TAG OUTSIDE LET *) in S' := (!S); S' end
    (* GEN BEGIN TAG OUTSIDE LET *) val insert = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set => (* GEN BEGIN FUNCTION EXPRESSION *) fn entry => (set := insert (!set, entry)) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insertLast = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set => (* GEN BEGIN FUNCTION EXPRESSION *) fn datum => (set := insertLast (!set, datum)) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insertList = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set => (* GEN BEGIN FUNCTION EXPRESSION *) fn list => (set := insertList (!set, list)) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val insertShadow = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set => (* GEN BEGIN FUNCTION EXPRESSION *) fn entry => (set := insertShadow (!set, entry)) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val isEmpty = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => isEmpty (!ordSet) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val last = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => last (!ordSet) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    
    (* GEN BEGIN TAG OUTSIDE LET *) val lookup = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (* GEN BEGIN FUNCTION EXPRESSION *) fn key => lookup (!ordSet) key (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val clear = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (ordSet := empty) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val app = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (* GEN BEGIN FUNCTION EXPRESSION *) fn f => app f (!ordSet) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val update = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (* GEN BEGIN FUNCTION EXPRESSION *) fn f => ((ordSet := (update f (!ordSet)); ordSet)) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val forall = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (* GEN BEGIN FUNCTION EXPRESSION *) fn f => forall (!ordSet) f (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val exists = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (* GEN BEGIN FUNCTION EXPRESSION *) fn f => exists (!ordSet) f (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val existsOpt = ((* GEN BEGIN FUNCTION EXPRESSION *) fn ordSet => (* GEN BEGIN FUNCTION EXPRESSION *) fn f => existsOpt (!ordSet) f (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    fun size S = setsize (!S) 

    (* GEN BEGIN TAG OUTSIDE LET *) val difference = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set1 => (* GEN BEGIN FUNCTION EXPRESSION *) fn set2 => (let (* GEN BEGIN TAG OUTSIDE LET *) val set = new() (* GEN END TAG OUTSIDE LET *) in set := difference (!set1, !set2); set end) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val difference2 = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set1 => (* GEN BEGIN FUNCTION EXPRESSION *) fn set2 => (let (* GEN BEGIN TAG OUTSIDE LET *) val r1 = new() (* GEN END TAG OUTSIDE LET *)
    					      (* GEN BEGIN TAG OUTSIDE LET *) val r2 = new() (* GEN END TAG OUTSIDE LET *) 
    					      (* GEN BEGIN TAG OUTSIDE LET *) val (rset1, rset2) = difference2 (!set1, !set2) (* GEN END TAG OUTSIDE LET *)
    					      in r1 := rset1; r2:= rset2 ;
    					      (r1, r2) end) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)


    (* GEN BEGIN TAG OUTSIDE LET *) val differenceModulo = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set1 => (* GEN BEGIN FUNCTION EXPRESSION *) fn set2 => (* GEN BEGIN FUNCTION EXPRESSION *) fn F => 
    			    (let (* GEN BEGIN TAG OUTSIDE LET *) val r1 = new() (* GEN END TAG OUTSIDE LET *)
    				 (* GEN BEGIN TAG OUTSIDE LET *) val r2 = new() (* GEN END TAG OUTSIDE LET *) 
    				 (* GEN BEGIN TAG OUTSIDE LET *) val (rset1, rset2) = diffMod F (!set1, !set2) (* GEN END TAG OUTSIDE LET *)
    			     in r1 := rset1; r2:= rset2 ;
    			       (r1, r2) end) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)


    (* GEN BEGIN TAG OUTSIDE LET *) val splitSets = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set1 => (* GEN BEGIN FUNCTION EXPRESSION *) fn set2 => (* GEN BEGIN FUNCTION EXPRESSION *) fn F => 
    		    (let (* GEN BEGIN TAG OUTSIDE LET *) val r1 = new() (* GEN END TAG OUTSIDE LET *)
    			 (* GEN BEGIN TAG OUTSIDE LET *) val r2 = new() (* GEN END TAG OUTSIDE LET *) 
    			 (* GEN BEGIN TAG OUTSIDE LET *) val r = new() (* GEN END TAG OUTSIDE LET *) 
    			 (* GEN BEGIN TAG OUTSIDE LET *) val (rset, rset1, rset2) = splitSets F (!set1, !set2) (* GEN END TAG OUTSIDE LET *)
    		     in r:= rset; r1 := rset1; r2:= rset2 ;
    		       (r, r1, r2) 
    		     end) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val intersection = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set1 => (* GEN BEGIN FUNCTION EXPRESSION *) fn set2 => (let (* GEN BEGIN TAG OUTSIDE LET *) val set = new() (* GEN END TAG OUTSIDE LET *) in set := intersection (!set1, !set2); set end) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val union = ((* GEN BEGIN FUNCTION EXPRESSION *) fn set1 => (* GEN BEGIN FUNCTION EXPRESSION *) fn set2 => (let (* GEN BEGIN TAG OUTSIDE LET *) val set = new() (* GEN END TAG OUTSIDE LET *) in set := union (!set1, !set2); set end) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *)) (* GEN END TAG OUTSIDE LET *)

  end
end;  (* functor RedBlackSet *)

