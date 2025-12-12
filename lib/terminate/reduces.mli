(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature REDUCES =
sig
  (*! structure IntSyn : INTSYN !*)
    
  exception Error of string

  val reset : unit -> unit
  val checkFamReduction : IntSyn.cid -> unit 
  val checkFam : IntSyn.cid -> unit   

end (* GEN END SIGNATURE DECLARATION *);  (* signature REDUCES *)
