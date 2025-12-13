(* Global parameters *)
(* Author: Frank Pfenning *)

structure Global :> GLOBAL =
struct

  (* GEN BEGIN TAG OUTSIDE LET *) val chatter = ref 3 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val style = ref 0 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxCid = 19999 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxMid = 999 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val maxCSid = 49 (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val doubleCheck = ref false (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val unsafe = ref false (* GEN END TAG OUTSIDE LET *)
  (* GEN BEGIN TAG OUTSIDE LET *) val autoFreeze = ref true (* GEN END TAG OUTSIDE LET *) (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *)
  (* GEN BEGIN TAG OUTSIDE LET *) val timeLimit = ref (NONE : (Time.time option)) (* GEN END TAG OUTSIDE LET *)

  fun chPrint n s = if !chatter >= n then print (s ()) else ()
  fun chMessage n s f = if !chatter >= n then f (s ()) else ()

end;  (* structure Global *)
