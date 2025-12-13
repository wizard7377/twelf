(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)

structure Ring :> RING =
struct

  exception Empty

  type 'a ring = 'a list * 'a list

  (* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)

  (* empty q = true if q = [], false otherwise *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) empty (nil, nil) = true (* GEN END CASE FIRST *) (* GEN END CASE FIRST *) 
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) empty _ = false (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* init l = l (as ring) *)
  fun init l = (nil, l)

  (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
  fun insert ((r, l), y) = (r, y :: l)

  (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) current (nil, nil) = raise Empty (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) current (_, x :: _) = x (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) current (l, nil) = current (nil, rev l) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) next (nil, nil) = raise Empty (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) next (r, nil) = next (nil, rev r) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) next (r, x :: l) = (x :: r, l) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) previous (nil, nil) = raise Empty (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) previous (nil, l) = previous (rev l, nil) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) previous (x :: r, l) = (r, x :: l) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) delete (nil, nil) = raise Empty (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) delete (r, nil) = delete (nil, rev r) (* GEN END CASE BRANCH *) 
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) delete (r, x :: l) = (r, l) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* foldr is inefficient *)
  fun foldr f i (r, l) = List.foldr f i (l @ rev r)

  (* order of map is undefined.  relevant? *)
  fun map f (r, l) = (List.map f r, List.map f l)

end;  (* structure Ring *)
