(* Recursion: Version 1.3 *)
(* Author: Carsten Schuermann *)

module type MTPRECURSION = 
sig
  module StateSyn : STATESYN

  exception Error of string

  type operator
    
  val expand : StateSyn.State -> operator 
  val apply : operator -> StateSyn.State
  val menu : operator -> string
end;  (* module type MTPRECURSION *)
