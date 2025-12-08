(* Basic search engine *)
(* Author: Carsten Schuermann *)

module type OLDSEARCH = 
sig
  module MetaSyn : METASYN

  exception Error of string

  val searchEx : 
      IntSyn.dctx * IntSyn.exp list
      * (IntSyn.exp * IntSyn.Sub)
      * (unit -> unit)
      -> MetaSyn.State list
    
  val searchAll : 
      IntSyn.dctx * IntSyn.exp list
      * (IntSyn.exp * IntSyn.Sub)
      * (MetaSyn.State list -> MetaSyn.State list)
      -> MetaSyn.State list
end;; (* module type SEARCH *)
