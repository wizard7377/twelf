(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)

module type TABLED =
sig

  (*! module IntSyn : INTSYN !*)
  (*! module CompSyn : COMPSYN !*)

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.pskeleton -> unit) -> unit

  val updateGlobalTable : (CompSyn.goal * bool) -> unit

  val keepTable : IntSyn.cid -> bool

  val fillTable : unit -> unit

  val nextStage : unit -> bool

  val reset : unit -> unit

  val tableSize : unit -> int

  val suspGoalNo : unit -> int

end;  (* module type TABLED *)

