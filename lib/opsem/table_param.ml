(* Table parameters *)
(* Author: Brigitte Pientka *)

module TableParam (module Global : GLOBAL
                    (*! module IntSyn' : INTSYN !*)
                    (*! module CompSyn' : COMPSYN !*)
                    (*!  sharing CompSyn'.IntSyn = IntSyn'!*)
                    (*! module RBSet : RBSET!*))
: TABLEPARAM =
struct

  (*! module IntSyn = IntSyn' !*)
  (*! module CompSyn = CompSyn' !*)
  (*! module RBSet = RBSet !*)

   exception Error of string

   type Strategy = Variant | Subsumption

   type ResEqn =
     Trivial                              (* trivially done *)
   | Unify of IntSyn.dctx * IntSyn.Exp    (* call unify *)
     * IntSyn.Exp * ResEqn

   type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub)
                               * CompSyn.pskeleton) list,
                  lookup: int} ref

   type Status = Complete | Incomplete

   (* globalTable stores the queries whose solution we want to keep *)
   let globalTable : (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx *
                       IntSyn.Exp * ResEqn * answer * Status ) list ref
                      = ref []

   fun resetGlobalTable () = (globalTable := [])

   fun emptyAnsw () = ref {solutions = [], lookup = 0}

   fun addSolution (S, answRef) =
     let
       let {solutions = SList, lookup = k} = !answRef
     in
       answRef := {solutions = (S::SList), lookup = k}
     end

   fun updateAnswLookup (k',answRef) =
     let
       let {solutions = SList, lookup = k} = !answRef
     in
       answRef := {solutions = SList, lookup = k'}
     end

   fun solutions (answ as ref {solutions = S, lookup = i}) = S
   fun lookup (answ as ref {solutions = S, lookup = i}) = i

   fun noAnswers answ =
     (case (List.take (solutions(answ), lookup(answ))) (*solutions(answ) *)
        of [] => true
      | L  => false)

   type asub = IntSyn.Exp RBSet.ordSet
   let aid : unit -> asub = RBSet.new


   type callCheckResult =
       NewEntry of answer
     | RepeatedEntry of (IntSyn.Sub * IntSyn.Sub) * answer * Status
     | DivergingEntry of (IntSyn.Sub * answer)

   type answState = new | repeated

(* ---------------------------------------------------------------------- *)
(* global search parameters *)

  let strategy  = ref Variant (* Subsumption *)

  let divHeuristic = ref false;
(*  let divHeuristic = ref true;*)

  let stageCtr = ref 0;

 (* term abstraction and ctx abstraction *)
 (* currently not used *)
  let termDepth = ref NONE : int option ref;
  let ctxDepth = ref NONE : int option ref;
  let ctxLength = ref NONE : int option ref;

  (* apply strengthening during abstraction *)
  let strengthen = ref false ;


end;; (* module TableParam *)

