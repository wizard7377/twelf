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

  fun (* GEN BEGIN FUN FIRST *) delete (nil, nil) = NONE (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) delete (inp, x::out) = SOME (x, (inp, out)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) delete (inp, nil) = delete (nil, List.rev inp) (* GEN END FUN BRANCH *)

  fun insertFront (x, (inp, out)) = (inp, x::out)

  fun (* GEN BEGIN FUN FIRST *) deleteEnd (nil, nil) = NONE (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) deleteEnd (x::inp, out) = SOME (x, (inp, out)) (* GEN END FUN BRANCH *)
    | (* GEN BEGIN FUN BRANCH *) deleteEnd (nil, out) = delete (List.rev out, nil) (* GEN END FUN BRANCH *)

  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
  (* toList q ==> (l, SOME(q')) means q == l == q' *)
  (* and toList q' is constant time *)
  fun (* GEN BEGIN FUN FIRST *) toList (nil, out) = (out, NONE) (* GEN END FUN FIRST *)
    | (* GEN BEGIN FUN BRANCH *) toList (inp, out) =
      let
    	(* GEN BEGIN TAG OUTSIDE LET *) val out' = out @ List.rev(inp) (* GEN END TAG OUTSIDE LET *)
      in
    	(out', SOME (nil, out'))
      end (* GEN END FUN BRANCH *)

end;  (* structure Queue *)
