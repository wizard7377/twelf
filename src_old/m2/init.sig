(* Initialization *)
(* Author: Carsten Schuermann *)

signature INIT = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  val init : IntSyn.cid list -> MetaSyn.state list
end;  (* signature INIT *)
