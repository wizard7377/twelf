(* Basic search engine: Version 1.3*)


(* Author: Carsten Schuermann *)


module type MTPSEARCH = sig
  module StateSyn : STATESYN
  exception Error of string
  val searchEx : int * IntSyn.exp list(*      * (IntSyn.Exp * IntSyn.Sub) *)
 * (int -> unit) -> unit

end


(* signature SEARCH *)

