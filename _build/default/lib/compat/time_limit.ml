(* Default implementation of timeLimit *)
(* Ignores time limit *)

structure TimeLimit :> TIME_LIMIT =
struct
  exception TimeOut
  (* GEN BEGIN TAG INSIDE LET *) val timeLimit = fn t => fn f => fn x => f(x) (* GEN END TAG INSIDE LET *)
end;
