(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPSPLITTING = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  type operator
    
  val expand : StateSyn.state -> operator list 
  val applicable : operator -> bool
  val apply : operator -> StateSyn.state list
  val menu : operator -> string
  val index : operator -> int
  val compare : operator * operator -> order
end (* GEN END SIGNATURE DECLARATION *);  (* signature MTPSPLITTING *)
