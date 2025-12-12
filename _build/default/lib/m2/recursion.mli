(* Recursion *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature RECURSION = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  type operator
    
  val expandLazy : MetaSyn.state -> operator list 
  val expandEager : MetaSyn.state -> operator list 

  val apply : operator -> MetaSyn.state

  val menu : operator -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature RECURSION *)
