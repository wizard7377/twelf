(* Initialization *)
(* Author: Carsten Schuermann *)

module type INIT = 
sig
  module MetaSyn : METASYN

  exception Error of string

  val init : IntSyn.cid list -> MetaSyn.State list
end;  (* module type INIT *)
