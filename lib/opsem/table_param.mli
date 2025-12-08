(* Global Table parameters *)
(* Author: Brigitte Pientka *)

module type TABLEPARAM =
sig
  (*! module IntSyn : INTSYN !*)
  (*! module CompSyn : COMPSYN !*)
  (*! module RBSet : RBSET !*)

  exception Error of string

  (* Residual equation *)
  type resEqn =
    Trivial				  (* trivially done *)
  | Unify of IntSyn.dctx * IntSyn.Exp     (* call unify *)
    * IntSyn.Exp * resEqn

  type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list,
		 lookup: int} ref
    
  type status = Complete | Incomplete

  val globalTable : (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * 
		      IntSyn.Exp * resEqn * answer * status ) list ref

  val resetGlobalTable : unit -> unit

  val emptyAnsw : unit -> answer

(* destructively updates answers *)
 val addSolution : ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) * answer 
                  -> unit

 val updateAnswLookup : int * answer -> unit

 val solutions : answer -> ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list
 val lookup : answer -> int
 val noAnswers : answer -> bool

(* ---------------------------------------------------------------------- *)
 type asub  = IntSyn.Exp RBSet.ordSet 

 val aid : unit -> asub

 type callCheckResult = 
    NewEntry of answer 
  | RepeatedEntry of (IntSyn.Sub * IntSyn.Sub) * answer * Status
  | DivergingEntry of IntSyn.Sub * answer

  type answState = new | repeated

(* ---------------------------------------------------------------------- *)

  type strategy = Variant | Subsumption


  val strategy  : Strategy ref 
  val stageCtr  : int ref
  val divHeuristic : bool ref;

  val termDepth  : int option ref
  val ctxDepth   : int option ref
  val ctxLength  : int option ref 

  val strengthen : bool ref

end;; (* module type TABLEPARAM *)
