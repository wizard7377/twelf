(* Compiled Syntax *)

(* Author: Iliano Cervesato *)

(* Modified: Jeff Polakow *)

module type COMPSYN = sig
  (*! structure IntSyn : INTSYN !*)
  type opt = No | LinearHeads | Indexing

  val optimize : opt ref

  type goal =
    | Atom of IntSyn.exp
    | Impl of
        resGoal
        * IntSyn.exp (*     | (r,A,a) => g         *)
        * IntSyn.head
        * goal
    | All of IntSyn.dec * goal

  and resGoal =
    | Eq of IntSyn.exp
    | Assign of IntSyn.exp * auxGoal
    | And of resGoal (*     | r & (A,g)            *) * IntSyn.exp * goal
    | In of resGoal (*     | r virt& (A,g)        *) * IntSyn.exp * goal
    | Exists of IntSyn.dec * resGoal
    | Axists of IntSyn.dec * resGoal

  and auxGoal =
    | Trivial
    | UnifyEq of
        IntSyn.dctx * IntSyn.exp (* call unify *) * IntSyn.exp * auxGoal

  (* Static programs -- compiled version for_sml substitution trees *)
  type conjunction = True | Conjunct of goal * IntSyn.exp * conjunction

  type compHead =
    | Head of (IntSyn.exp * IntSyn.dec IntSyn.ctx * auxGoal * IntSyn.cid)

  (* pskeleton instead of proof term *)
  type flatterm = Pc of int | Dc of int | Csolver of IntSyn.exp
  type pskeleton = flatterm list

  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)
  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  type comDec =
    | Parameter
    | Dec of resGoal * IntSyn.sub * IntSyn.head
    | BDec of resGoal * IntSyn.sub * IntSyn.head list
    | PDec

  (* Dynamic programs: context with synchronous clause pool *)
  type dProg = DProg of (IntSyn.dctx * comDec IntSyn.ctx)

  (* Programs --- compiled version of the signature (no direct head access) *)
  type conDec = SClause of resGoal | Void

  (* Other declarations are ignored  *)
  (* Install Programs (without indexing) *)
  val sProgInstall : IntSyn.cid * conDec -> unit
  val sProgLookup : IntSyn.cid -> conDec
  val sProgReset : unit -> unit

  (* Deterministic flag *)
  val detTableInsert : IntSyn.cid * bool -> unit
  val detTableCheck : IntSyn.cid -> bool
  val detTableReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub : goal * IntSyn.sub -> goal
  val resGoalSub : resGoal * IntSyn.sub -> resGoal
  val pskeletonToString : pskeleton -> string
end

(* signature COMPSYN *)
