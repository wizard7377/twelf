(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)

(Ring : RIN)G =
struct

  exception Empty

  type 'a ring = 'a list * 'a list

  (* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)

  (* empty q = true if q = [], false otherwise *)
  let rec empty = function (nil, nil) -> true 
    | _ -> false

  (* init l = l (as ring) *)
  fun init l = (nil, l)

  (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
  fun insert ((r, l), y) = (r, y :: l)

  (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
  let rec current = function (nil, nil) -> raise Empty
    | (_, x :: _) -> x
    | (l, nil) -> current (nil, rev l)

  (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  let rec next = function (nil, nil) -> raise Empty
    | (r, nil) -> next (nil, rev r)
    | (r, x :: l) -> (x :: r, l)

  (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  let rec previous = function (nil, nil) -> raise Empty
    | (nil, l) -> previous (rev l, nil)
    | (x :: r, l) -> (r, x :: l)

  (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
  let rec delete = function (nil, nil) -> raise Empty
    | (r, nil) -> delete (nil, rev r) 
    | (r, x :: l) -> (r, l)

  (* foldr is inefficient *)
  fun foldr f i (r, l) = List.foldr f i (l @ rev r)

  (* order of map is undefined.  relevant? *)
  fun map f (r, l) = (List.map f r, List.map f l)

end;; (* module Ring *)
