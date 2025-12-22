(* Table parameters *)

(* Author: Brigitte Pientka *)

module TableParam (Global : GLOBAL) : TABLEPARAM = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure CompSyn = CompSyn' !*)

  (*! structure RBSet = RBSet !*)

  exception Error of string

  type strategy = Variant | Subsumption

  type resEqn =
    | Trivial
    | Unify of IntSyn.dctx * IntSyn.exp (* call unify *) * IntSyn.exp * resEqn

  type answer =
    < solutions : (IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton list
    ; lookup : int >
    ref

  type status = Complete | Incomplete
  (* globalTable stores the queries whose solution we want to keep *)

  let globalTable :
      IntSyn.dctx
      * IntSyn.dctx
      * IntSyn.dctx
      * IntSyn.exp
      * resEqn
      * answer
      * status list ref =
    ref []

  let rec resetGlobalTable () = globalTable := []
  let rec emptyAnsw () = ref { solutions = []; lookup = 0 }

  let rec addSolution (S, answRef) =
    let { solutions = SList; lookup = k } = !answRef in
    answRef := { solutions = S :: SList; lookup = k }

  let rec updateAnswLookup (k', answRef) =
    let { solutions = SList; lookup = k } = !answRef in
    answRef := { solutions = SList; lookup = k' }

  let rec solutions answ = S
  let rec lookup answ = i

  let rec noAnswers answ =
    match List.take (solutions answ, lookup answ) (*solutions(answ) *) with
    | [] -> true
    | L -> false

  type asub = IntSyn.exp RBSet.ordSet

  let aid : unit -> asub = RBSet.new_

  type callCheckResult =
    | NewEntry of answer
    | RepeatedEntry of (IntSyn.sub * IntSyn.sub) * answer * status
    | DivergingEntry of (IntSyn.sub * answer)

  type answState = New_ | Repeated
  (* ---------------------------------------------------------------------- *)

  (* global search parameters *)

  let strategy = ref Variant
  (* Subsumption *)

  let divHeuristic = ref false
  (*  val divHeuristic = ref true;*)

  let stageCtr = ref 0
  (* term abstraction and ctx abstraction *)

  (* currently not used *)

  let termDepth = (ref None : int option ref)
  let ctxDepth = (ref None : int option ref)
  let ctxLength = (ref None : int option ref)
  (* apply strengthening during abstraction *)

  let strengthen = ref false
end

(* structure TableParam *)
(* Global Table parameters *)

(* Author: Brigitte Pientka *)

module type TABLEPARAM = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure RBSet : RBSET !*)
  exception Error of string

  (* Residual equation *)
  type resEqn =
    | Trivial
    | Unify of IntSyn.dctx * IntSyn.exp (* call unify *) * IntSyn.exp * resEqn

  type answer =
    < solutions : (IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton list
    ; lookup : int >
    ref

  type status = Complete | Incomplete

  val globalTable :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * resEqn
    * answer
    * status list ref

  val resetGlobalTable : unit -> unit
  val emptyAnsw : unit -> answer

  (* destructively updates answers *)
  val addSolution :
    ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) * answer -> unit

  val updateAnswLookup : int * answer -> unit
  val solutions : answer -> (IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton list
  val lookup : answer -> int
  val noAnswers : answer -> bool

  (* ---------------------------------------------------------------------- *)
  type asub = IntSyn.exp RBSet.ordSet

  val aid : unit -> asub

  type callCheckResult =
    | NewEntry of answer
    | RepeatedEntry of (IntSyn.sub * IntSyn.sub) * answer * status
    | DivergingEntry of IntSyn.sub * answer

  type answState = New_ | Repeated

  (* ---------------------------------------------------------------------- *)
  type strategy = Variant | Subsumption

  val strategy : strategy ref
  val stageCtr : int ref
  val divHeuristic : bool ref
  val termDepth : int option ref
  val ctxDepth : int option ref
  val ctxLength : int option ref
  val strengthen : bool ref
end

(* signature TABLEPARAM *)
