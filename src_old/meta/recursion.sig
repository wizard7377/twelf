(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPRECURSION = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  type operator
    
  val expand : StateSyn.state -> operator 
  val apply : operator -> StateSyn.state
  val menu : operator -> string
end;  (* signature MTPRECURSION *)
