(* Basic search engine *)
(* Author: Carsten Schuermann *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature OLDSEARCH = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  val searchEx : 
      IntSyn.dctx * IntSyn.exp list
      * (IntSyn.exp * IntSyn.sub)
      * (unit -> unit)
      -> MetaSyn.state list
    
  val searchAll : 
      IntSyn.dctx * IntSyn.exp list
      * (IntSyn.exp * IntSyn.sub)
      * (MetaSyn.state list -> MetaSyn.state list)
      -> MetaSyn.state list
end (* GEN END SIGNATURE DECLARATION *);  (* signature SEARCH *)
