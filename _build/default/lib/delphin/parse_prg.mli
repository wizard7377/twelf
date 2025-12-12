(* The Parser *)
(* Author: Richard Fontana *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature PARSE =
sig
  
  structure DextSyn  : DEXTSYN
    
  val fparse : string -> unit
  val gparse : string -> DextSyn.ast
  val sparse : unit -> DextSyn.ast

end (* GEN END SIGNATURE DECLARATION *)  (* signature PARSE *)
