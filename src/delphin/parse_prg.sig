(* The Parser *)
(* Author: Richard Fontana *)

signature PARSE =
sig
  
  structure DextSyn  : DEXTSYN
    
  val fparse : string -> unit
  val gparse : string -> DextSyn.ast
  val sparse : unit -> DextSyn.ast

end  (* signature PARSE *)
