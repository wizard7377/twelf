(* Queues *)
(* Author: Frank Pfenning *)
(* Standard functional implementation of queues *)
(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)

(Queue : QUEU)E =
struct

  (* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)
  type 'a queue = 'a list * 'a list

  let empty = (nil, nil)

  fun insert (x, (inp, out)) = (x::inp, out)

  let rec delete = function (nil, nil) -> NONE
    | (inp, x::out) -> SOME (x, (inp, out))
    | (inp, nil) -> delete (nil, List.rev inp)

  fun insertFront (x, (inp, out)) = (inp, x::out)

  let rec deleteEnd = function (nil, nil) -> NONE
    | (x::inp, out) -> SOME (x, (inp, out))
    | (nil, out) -> delete (List.rev out, nil)

  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
  (* toList q ==> (l, SOME(q')) means q == l == q' *)
  (* and toList q' is constant time *)
  let rec toList = function (nil, out) -> (out, NONE)
    | (inp, out) -> 
      let
	let out' = out @ List.rev(inp)
      in
	(out', SOME (nil, out'))
      end

end;; (* module Queue *)
