(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPRECURSION = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  type operator
    
  val expand : StateSyn.state -> operator 
  val apply : operator -> StateSyn.state
  val menu : operator -> string
end (* GEN END SIGNATURE DECLARATION *);  (* signature MTPRECURSION *)
