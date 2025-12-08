(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

module type COMPSYN =
sig

  (*! module IntSyn : INTSYN !*)

  type opt = No | LinearHeads | Indexing 

  val optimize : Opt ref

  type goal =                       (* Goals                      *)
    Atom of IntSyn.exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.exp        (*     | (r,A,a) => g         *)
            * IntSyn.Head * goal		
  | All  of IntSyn.Dec * goal           (*     | all x:A. g           *)

  (* dynamic clauses *)
  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.exp                (* r ::= p = ?                *)
  | Assign of IntSyn.exp * AuxGoal      (*     | p = ?, where p has   *)
					(* only new vars,             *)  
                                        (* then unify all the vars    *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.exp * Goal       
  | In   of ResGoal			(*     | r virt& (A,g)        *)
              * IntSyn.exp * Goal       
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)
  | Axists of IntSyn.Dec * ResGoal	(*     | exists x:_. r        *)

  and AuxGoal =
    Trivial				  (* trivially done *)
  | UnifyEq of IntSyn.dctx * IntSyn.exp   (* call unify *)
             * IntSyn.exp * AuxGoal


  (* Static programs -- compiled version for substitution trees *)

  type conjunction = True | Conjunct of goal * IntSyn.exp * conjunction

  type compHead = 
     Head of (IntSyn.exp * IntSyn.Dec IntSyn.ctx * AuxGoal * IntSyn.cid)

 (* pskeleton instead of proof term *)
  type flatterm = 
    Pc of int | Dc of int | Csolver of IntSyn.exp

  type pskeleton = Flatterm list  

  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.ctx *)

  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  type comDec
  = Parameter
  | Dec of ResGoal * IntSyn.Sub * IntSyn.Head
  | BDec of (ResGoal * IntSyn.Sub * IntSyn.Head) list
  | PDec

  (* Dynamic programs: context with synchronous clause pool *)
  type dProg = DProg of (IntSyn.dctx * comDec IntSyn.ctx)

  (* Programs --- compiled version of the module type (no direct head access) *)
  type conDec =			      (* Compiled constant declaration *)
       SClause of ResGoal                     (* c : A  -- static clause (residual goal) *)
    | Void 		                      (* Other declarations are ignored  *)


  (* Install Programs (without indexing) *)
  val sProgInstall : IntSyn.cid * ConDec -> unit  

  val sProgLookup: IntSyn.cid -> ConDec
  val sProgReset : unit -> unit

  (* Deterministic flag *)
  val detTableInsert : IntSyn.cid * bool -> unit
  val detTableCheck : IntSyn.cid -> bool
  val detTableReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub   : Goal * IntSyn.Sub -> Goal
  val resGoalSub: ResGoal * IntSyn.Sub -> ResGoal
  
  val pskeletonToString: pskeleton -> string

end;; (* module type COMPSYN *)
