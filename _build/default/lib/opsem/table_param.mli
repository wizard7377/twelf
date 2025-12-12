(* Global Table parameters *)
(* Author: Brigitte Pientka *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature TABLEPARAM =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure RBSet : RBSET !*)

  exception Error of string

  (* Residual equation *)
  datatype res_eqn =
    Trivial				  (* trivially done *)
  | Unify of IntSyn.dctx * IntSyn.exp     (* call unify *)
    * IntSyn.exp * res_eqn

  type answer = {solutions : ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) list,
		 lookup: int} ref
    
  datatype status = Complete | Incomplete

  val globalTable : (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * 
		      IntSyn.exp * res_eqn * answer * status ) list ref

  val resetGlobalTable : unit -> unit

  val emptyAnsw : unit -> answer

(* destructively updates answers *)
 val addSolution : ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) * answer 
                  -> unit

 val updateAnswLookup : int * answer -> unit

 val solutions : answer -> ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) list
 val lookup : answer -> int
 val noAnswers : answer -> bool

(* ---------------------------------------------------------------------- *)
 type asub  = IntSyn.exp RBSet.ord_set 

 val aid : unit -> asub

 datatype call_check_result = 
    NewEntry of answer 
  | RepeatedEntry of (IntSyn.sub * IntSyn.sub) * answer * status
  | DivergingEntry of IntSyn.sub * answer

  datatype answ_state = new | repeated

(* ---------------------------------------------------------------------- *)

  datatype strategy = Variant | Subsumption


  val strategy  : strategy ref 
  val stageCtr  : int ref
  val divHeuristic : bool ref;

  val termDepth  : int option ref
  val ctxDepth   : int option ref
  val ctxLength  : int option ref 

  val strengthen : bool ref

end (* GEN END SIGNATURE DECLARATION *);  (* signature TABLEPARAM *)
