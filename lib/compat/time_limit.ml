(* Default implementation of timeLimit *)
(* Ignores time limit *)

structure TimeLimit :> TIME_LIMIT =
struct
  exception TimeOut
  (* GEN BEGIN TAG OUTSIDE LET *) val timeLimit = (* GEN BEGIN FUNCTION EXPRESSION *) fn t => (* GEN BEGIN FUNCTION EXPRESSION *) fn f => (* GEN BEGIN FUNCTION EXPRESSION *) fn x => f(x) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *) (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
end;
