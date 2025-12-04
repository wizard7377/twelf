(* The Parser *)
(* Author: Richard Fontana *)

module type PARSE =
sig
  
  module DextSyn  : DEXTSYN
    
  val fparse : string -> unit
  val gparse : string -> DextSyn.ast
  val sparse : unit -> DextSyn.ast

end  (* module type PARSE *)
