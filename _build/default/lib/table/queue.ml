(* Queues *)
(* Author: Frank Pfenning *)
(* Standard functional implementation of queues *)
(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)

structure Queue :> QUEUE =
struct

  (* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)
  type 'a queue = 'a list * 'a list

  (* GEN BEGIN TAG INSIDE LET *) val empty = (nil, nil) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun insert (x, (inp, out)) = (x::inp, out) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun delete (nil, nil) = NONE
    | delete (inp, x::out) = SOME (x, (inp, out))
    | delete (inp, nil) = delete (nil, List.rev inp) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun insertFront (x, (inp, out)) = (inp, x::out) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun deleteEnd (nil, nil) = NONE
    | deleteEnd (x::inp, out) = SOME (x, (inp, out))
    | deleteEnd (nil, out) = delete (List.rev out, nil) (* GEN END TAG INSIDE LET *)

  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
  (* toList q ==> (l, SOME(q')) means q == l == q' *)
  (* and toList q' is constant time *)
  (* GEN BEGIN TAG INSIDE LET *) fun toList (nil, out) = (out, NONE)
    | toList (inp, out) =
      let
    	val out' = out @ List.rev(inp)
      in
    	(out', SOME (nil, out'))
      end (* GEN END TAG INSIDE LET *)

end;  (* structure Queue *)
