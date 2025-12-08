(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)

module type REDUCES =
sig
  (*! module IntSyn : INTSYN !*)
    
  exception Error of string

  val reset : unit -> unit
  val checkFamReduction : IntSyn.cid -> unit 
  val checkFam : IntSyn.cid -> unit   

end;; (* module type REDUCES *)
