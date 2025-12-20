(* Initialization *)


(* Author: Carsten Schuermann *)


module type INIT = sig
  module MetaSyn : METASYN
  exception Error of string
  val init : IntSyn.cid list -> MetaSyn.state list

end


(* signature INIT *)

