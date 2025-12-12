(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature MTPSEARCH = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  val searchEx : int * IntSyn.exp list
(*      * (IntSyn.Exp * IntSyn.Sub) *)
      * (int -> unit) -> unit
end (* GEN END SIGNATURE DECLARATION *);  (* signature SEARCH *)
