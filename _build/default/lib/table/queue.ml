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

  (* GEN BEGIN TAG OUTSIDE LET *) val empty = (nil, nil) (* GEN END TAG OUTSIDE LET *)

  fun insert (x, (inp, out)) = (x::inp, out)

  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) delete (nil, nil) = NONE (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) delete (inp, x::out) = SOME (x, (inp, out)) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) delete (inp, nil) = delete (nil, List.rev inp) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  fun insertFront (x, (inp, out)) = (inp, x::out)

  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) deleteEnd (nil, nil) = NONE (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) deleteEnd (x::inp, out) = SOME (x, (inp, out)) (* GEN END CASE BRANCH *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) deleteEnd (nil, out) = delete (List.rev out, nil) (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
  (* toList q ==> (l, SOME(q')) means q == l == q' *)
  (* and toList q' is constant time *)
  fun (* GEN BEGIN CASE FIRST *) (* GEN BEGIN CASE FIRST *) toList (nil, out) = (out, NONE) (* GEN END CASE FIRST *) (* GEN END CASE FIRST *)
    | (* GEN BEGIN CASE BRANCH *) (* GEN BEGIN CASE BRANCH *) toList (inp, out) =
      let
    	val out' = out @ List.rev(inp)
      in
    	(out', SOME (nil, out'))
      end (* GEN END CASE BRANCH *) (* GEN END CASE BRANCH *)

end;  (* structure Queue *)
