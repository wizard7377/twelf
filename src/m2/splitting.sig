(* Splitting *)
(* Author: Carsten Schuermann *)

signature SPLITTING = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  type operator
    
  val expand : MetaSyn.state -> operator list 
  val apply : operator -> MetaSyn.state list

  val var : operator -> int
  val menu : operator -> string
  val index : operator -> int
end;  (* signature SPLITTING *)
