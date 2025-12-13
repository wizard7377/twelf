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
  fun (* GEN BEGIN FUN FIRST *) empty (nil, nil) = true (* GEN END FUN FIRST *) 
    | (* GEN BEGIN FUN BRANCH *) empty _ = false (* GEN END FUN BRANCH *)

  (* init l = l (as ring) *)
  fun init l = (nil, l)

  (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
  fun insert ((r, l), y) = (r, y :: l)

  (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
  fun (* GEN BEGIN FUN FIRST *) current (nil, nil) = raise Empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) current (_, x :: _) = x (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) current (l, nil) = current (nil, rev l) (* GEN END FUN BRANCH *)

  (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  fun (* GEN BEGIN FUN FIRST *) next (nil, nil) = raise Empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) next (r, nil) = next (nil, rev r) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) next (r, x :: l) = (x :: r, l) (* GEN END FUN BRANCH *)

  (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  fun (* GEN BEGIN FUN FIRST *) previous (nil, nil) = raise Empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) previous (nil, l) = previous (rev l, nil) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) previous (x :: r, l) = (r, x :: l) (* GEN END FUN BRANCH *)

  (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
  fun (* GEN BEGIN FUN FIRST *) delete (nil, nil) = raise Empty (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) delete (r, nil) = delete (nil, rev r) (* GEN END FUN BRANCH *) 
    | (* GEN BEGIN FUN BRANCH *) delete (r, x :: l) = (r, l) (* GEN END FUN BRANCH *)

  (* foldr is inefficient *)
  fun foldr f i (r, l) = List.foldr f i (l @ rev r)

  (* order of map is undefined.  relevant? *)
  fun map f (r, l) = (List.map f r, List.map f l)

end;  (* structure Ring *)
