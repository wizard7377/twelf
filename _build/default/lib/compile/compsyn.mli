(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

(* GEN BEGIN SIGNATURE DECLARATION *) signature COMPSYN =
sig

  (*! structure IntSyn : INTSYN !*)

  datatype opt = No | LinearHeads | Indexing 

  val optimize : opt ref

  datatype goal =                       (* Goals                      *)
    Atom of IntSyn.exp                  (* g ::= p                    *)
  | Impl of res_goal * IntSyn.exp        (*     | (r,A,a) => g         *)
            * IntSyn.head * goal		
  | All  of IntSyn.dec * goal           (*     | all x:A. g           *)

  (* dynamic clauses *)
  and res_goal =                         (* Residual Goals             *)
    Eq     of IntSyn.exp                (* r ::= p = ?                *)
  | Assign of IntSyn.exp * aux_goal      (*     | p = ?, where p has   *)
					(* only new vars,             *)  
                                        (* then unify all the vars    *)
  | And    of res_goal                   (*     | r & (A,g)            *)
              * IntSyn.exp * goal       
  | In   of res_goal			(*     | r virt& (A,g)        *)
              * IntSyn.exp * goal       
  | Exists of IntSyn.dec * res_goal      (*     | exists x:A. r        *)
  | Axists of IntSyn.dec * res_goal	(*     | exists x:_. r        *)

  and aux_goal =
    Trivial				  (* trivially done *)
  | UnifyEq of IntSyn.dctx * IntSyn.exp   (* call unify *)
             * IntSyn.exp * aux_goal


  (* Static programs -- compiled version for substitution trees *)

  datatype conjunction = True | Conjunct of goal * IntSyn.exp * conjunction

  datatype comp_head = 
     Head of (IntSyn.exp * IntSyn.dec IntSyn.ctx * aux_goal * IntSyn.cid)

 (* pskeleton instead of proof term *)
  datatype flatterm = 
    Pc of int | Dc of int | Csolver of IntSyn.exp

  type pskeleton = flatterm list  

  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)

  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  datatype com_dec
  = Parameter
  | Dec of res_goal * IntSyn.sub * IntSyn.head
  | BDec of (res_goal * IntSyn.sub * IntSyn.head) list
  | PDec

  (* Dynamic programs: context with synchronous clause pool *)
  datatype d_prog = DProg of (IntSyn.dctx * com_dec IntSyn.ctx)

  (* Programs --- compiled version of the signature (no direct head access) *)
  datatype con_dec =			      (* Compiled constant declaration *)
       SClause of res_goal                     (* c : A  -- static clause (residual goal) *)
    | Void 		                      (* Other declarations are ignored  *)


  (* Install Programs (without indexing) *)
  val sProgInstall : IntSyn.cid * con_dec -> unit  

  val sProgLookup: IntSyn.cid -> con_dec
  val sProgReset : unit -> unit

  (* Deterministic flag *)
  val detTableInsert : IntSyn.cid * bool -> unit
  val detTableCheck : IntSyn.cid -> bool
  val detTableReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub   : goal * IntSyn.sub -> goal
  val resGoalSub: res_goal * IntSyn.sub -> res_goal
  
  val pskeletonToString: pskeleton -> string

end (* GEN END SIGNATURE DECLARATION *);  (* signature COMPSYN *)
