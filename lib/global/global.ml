(* Global parameters *)
(* Author: Frank Pfenning *)

structure Global :> GLOBAL =
struct

  (* GEN BEGIN TAG INSIDE LET *) val chatter = ref 3 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val style = ref 0 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val maxCid = 19999 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val maxMid = 999 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val maxCSid = 49 (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val doubleCheck = ref false (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val unsafe = ref false (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) val autoFreeze = ref true (* GEN END TAG INSIDE LET *) (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *)
  (* GEN BEGIN TAG INSIDE LET *) val timeLimit = ref (NONE : (Time.time option)) (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun chPrint n s = if !chatter >= n then print (s ()) else () (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) fun chMessage n s f = if !chatter >= n then f (s ()) else () (* GEN END TAG INSIDE LET *)

end;  (* structure Global *)
