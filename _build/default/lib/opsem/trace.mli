(* GEN BEGIN SIGNATURE DECLARATION *) signature TRACE =
sig

  (* Program interface *)
  (*! structure IntSyn : INTSYN !*)

  type goal_tag
  val tagGoal : unit -> goal_tag

  datatype event =
    IntroHyp of IntSyn.head * IntSyn.dec
  | DischargeHyp of IntSyn.head * IntSyn.dec

  | IntroParm of IntSyn.head * IntSyn.dec
  | DischargeParm of IntSyn.head * IntSyn.dec

  | Resolved of IntSyn.head * IntSyn.head (* resolved with clause c, fam a *)
  | Subgoal of (IntSyn.head * IntSyn.head) * (unit -> int) (* clause c, fam a, nth subgoal *)

  | SolveGoal of goal_tag * IntSyn.head * IntSyn.exp
  | SucceedGoal of goal_tag * (IntSyn.head * IntSyn.head) * IntSyn.exp
  | CommitGoal of goal_tag * (IntSyn.head * IntSyn.head) * IntSyn.exp
  | RetryGoal of goal_tag * (IntSyn.head * IntSyn.head) * IntSyn.exp
  | FailGoal of goal_tag * IntSyn.head * IntSyn.exp

  | Unify of (IntSyn.head * IntSyn.head) * IntSyn.exp * IntSyn.exp (* clause head == goal *)
  | FailUnify of (IntSyn.head * IntSyn.head) * string (* failure message *)

  val signal : IntSyn.dctx * event -> unit
  val init : unit -> unit		(* initialize trace, break and tag *)

  val tracing : unit -> bool            (* currently tracing or using breakpoints *)

  (* User interface *)
  datatype 'a spec =
    None
  | Some of 'a list
  | All

  val trace : string spec -> unit
  val break : string spec -> unit
  val detail : int ref			(* 0 = none, 1 = default, 2 = unify *)

  val show : unit -> unit		(* show trace, break, detail *)
  val reset : unit -> unit		(* reset trace, break, detail *)

end (* GEN END SIGNATURE DECLARATION *);  (* signature TRACE *)
