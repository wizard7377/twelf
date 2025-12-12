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
  (* GEN BEGIN TAG INSIDE LET *) fun empty (nil, nil) = true 
    | empty _ = false (* GEN END TAG INSIDE LET *)

  (* init l = l (as ring) *)
  (* GEN BEGIN TAG INSIDE LET *) fun init l = (nil, l) (* GEN END TAG INSIDE LET *)

  (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
  (* GEN BEGIN TAG INSIDE LET *) fun insert ((r, l), y) = (r, y :: l) (* GEN END TAG INSIDE LET *)

  (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
  (* GEN BEGIN TAG INSIDE LET *) fun current (nil, nil) = raise Empty
    | current (_, x :: _) = x
    | current (l, nil) = current (nil, rev l) (* GEN END TAG INSIDE LET *)

  (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  (* GEN BEGIN TAG INSIDE LET *) fun next (nil, nil) = raise Empty
    | next (r, nil) = next (nil, rev r)
    | next (r, x :: l) = (x :: r, l) (* GEN END TAG INSIDE LET *)

  (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  (* GEN BEGIN TAG INSIDE LET *) fun previous (nil, nil) = raise Empty
    | previous (nil, l) = previous (rev l, nil)
    | previous (x :: r, l) = (r, x :: l) (* GEN END TAG INSIDE LET *)

  (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
  (* GEN BEGIN TAG INSIDE LET *) fun delete (nil, nil) = raise Empty
    | delete (r, nil) = delete (nil, rev r) 
    | delete (r, x :: l) = (r, l) (* GEN END TAG INSIDE LET *)

  (* foldr is inefficient *)
  (* GEN BEGIN TAG INSIDE LET *) fun foldr f i (r, l) = List.foldr f i (l @ rev r) (* GEN END TAG INSIDE LET *)

  (* order of map is undefined.  relevant? *)
  (* GEN BEGIN TAG INSIDE LET *) fun map f (r, l) = (List.map f r, List.map f l) (* GEN END TAG INSIDE LET *)

end;  (* structure Ring *)
