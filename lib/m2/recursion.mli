(* Recursion *)


(* Author: Carsten Schuermann *)


module type RECURSION = sig
  module MetaSyn : METASYN
  exception Error of string
  type operator
  val expandLazy : MetaSyn.state -> operator list
  val expandEager : MetaSyn.state -> operator list
  val apply : operator -> MetaSyn.state
  val menu : operator -> string

end


(* signature RECURSION *)

