(* Not Trailing Abstract Operations *)
(* Author: Roberto Virga *)

structure NoTrail : TRAIL =
struct

  type 'a trail = unit

  (* GEN BEGIN TAG INSIDE LET *) fun trail () = () (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun suspend ((), copy) = () (* GEN END TAG INSIDE LET *)
  (* GEN BEGIN TAG INSIDE LET *) fun resume ((),(), reset) = () (* GEN END TAG INSIDE LET *)
  
  (* GEN BEGIN TAG INSIDE LET *) fun reset () = () (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun mark () = () (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun unwind ((), undo) = () (* GEN END TAG INSIDE LET *)

  (* GEN BEGIN TAG INSIDE LET *) fun log ((), action) = () (* GEN END TAG INSIDE LET *)
end; (* structure NoTrail *)
