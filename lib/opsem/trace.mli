module type TRACE =
sig

  (* Program interface *)
  (*! module IntSyn : INTSYN !*)

  type goalTag
  val tagGoal : unit -> goalTag

  type event =
    IntroHyp of IntSyn.Head * IntSyn.Dec
  | DischargeHyp of IntSyn.Head * IntSyn.Dec

  | IntroParm of IntSyn.Head * IntSyn.Dec
  | DischargeParm of IntSyn.Head * IntSyn.Dec

  | Resolved of IntSyn.Head * IntSyn.Head (* resolved with clause c, fam a *)
  | Subgoal of (IntSyn.Head * IntSyn.Head) * (unit -> int) (* clause c, fam a, nth subgoal *)

  | SolveGoal of goalTag * IntSyn.Head * IntSyn.exp
  | SucceedGoal of goalTag * (IntSyn.Head * IntSyn.Head) * IntSyn.exp
  | CommitGoal of goalTag * (IntSyn.Head * IntSyn.Head) * IntSyn.exp
  | RetryGoal of goalTag * (IntSyn.Head * IntSyn.Head) * IntSyn.exp
  | FailGoal of goalTag * IntSyn.Head * IntSyn.exp

  | Unify of (IntSyn.Head * IntSyn.Head) * IntSyn.exp * IntSyn.exp (* clause head == goal *)
  | FailUnify of (IntSyn.Head * IntSyn.Head) * string (* failure message *)

  val signal : IntSyn.dctx * Event -> unit
  val init : unit -> unit		(* initialize trace, break and tag *)

  val tracing : unit -> bool            (* currently tracing or using breakpoints *)

  (* User interface *)
  type 'a Spec =
    None
  | Some of 'a list
  | All

  val trace : string Spec -> unit
  val break : string Spec -> unit
  val detail : int ref			(* 0 = none, 1 = default, 2 = unify *)

  val show : unit -> unit		(* show trace, break, detail *)
  val reset : unit -> unit		(* reset trace, break, detail *)

end;; (* module type TRACE *)
