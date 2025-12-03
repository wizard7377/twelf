(* Recursion *)
(* Author: Carsten Schuermann *)

module type RECURSION = 
sig
  module MetaSyn : METASYN

  exception Error of string

  type operator
    
  val expandLazy : MetaSyn.State -> operator list 
  val expandEager : MetaSyn.State -> operator list 

  val apply : operator -> MetaSyn.State

  val menu : operator -> string
end;  (* module type RECURSION *)
