(* Splitting *)
(* Author: Carsten Schuermann *)

module type SPLITTING = 
sig
  module MetaSyn : METASYN

  exception Error of string

  type operator
    
  val expand : MetaSyn.state -> operator list 
  val apply : operator -> MetaSyn.state list

  val var : operator -> int
  val menu : operator -> string
  val index : operator -> int
end;; (* module type SPLITTING *)
