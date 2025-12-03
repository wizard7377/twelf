(* The Parser *)
(* Author: Richard Fontana *)

module type PARSE =
sig
  
  module DextSyn  : DEXTSYN
    
  val fparse : string -> unit
  val gparse : string -> DextSyn.Ast
  val sparse : unit -> DextSyn.Ast

end  (* module type PARSE *)
