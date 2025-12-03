(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPSPLITTING = 
sig
  module StateSyn : STATESYN

  exception Error of string

  type operator
    
  val expand : StateSyn.State -> operator list 
  val applicable : operator -> bool
  val apply : operator -> StateSyn.State list
  val menu : operator -> string
  val index : operator -> int
  val compare : operator * operator -> order
end;  (* module type MTPSPLITTING *)
