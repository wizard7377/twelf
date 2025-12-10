(* Table parameters *)
(* Author: Brigitte Pientka *)

module TableParam (Global : GLOBAL)
                    (*! module IntSyn' : INTSYN !*)
                    (*! module CompSyn' : COMPSYN !*)
                    (*!  sharing CompSyn'.IntSyn = IntSyn'!*)
                    (*! (RBSet : RBSET)!*))
: TABLEPARAM =
struct

  (*! module IntSyn = IntSyn' !*)
  (*! module CompSyn = CompSyn' !*)
  (*! module RBSet = RBSet !*)

   exception Error of string

   type strategy = Variant | Subsumption

   type reseqn =
     Trivial                              (* trivially done *)
   | Unify of IntSyn.dctx * IntSyn.exp    (* call unify *)
     * IntSyn.exp * reseqn

   type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub)
                               * CompSyn.pskeleton) list,
                  lookup: int} ref

   type status = Complete | Incomplete

   (* globalTable stores the queries whose solution we want to keep *)
   let globalTable : (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx *
                       IntSyn.exp * resEqn * answer * status ) list ref
                      = ref []

   let rec resetGlobalTable () = (globalTable := [])

   let rec emptyAnsw () = ref {solutions = [], lookup = 0}

   let rec addSolution (S, answRef) =
     let
       let {solutions = SList, lookup = k} = !answRef
     in
       answRef := {solutions = (S::SList), lookup = k}
     end

   let rec updateAnswLookup (k',answRef) =
     let
       let {solutions = SList, lookup = k} = !answRef
     in
       answRef := {solutions = SList, lookup = k'}
     end

   let rec solutions (answ as ref {solutions = S, lookup = i}) = S
   let rec lookup (answ as ref {solutions = S, lookup = i}) = i

   let rec noAnswers answ =
     (case (List.take (solutions(answ), lookup(answ))) (*solutions(answ) *)
        of [] => true
      | L  => false)

   type asub = IntSyn.exp RBSet.ordSet
   let aid : unit -> asub = RBSet.new


   type callcheckresult =
       NewEntry of answer
     | RepeatedEntry of (IntSyn.Sub * IntSyn.Sub) * answer * status
     | DivergingEntry of (IntSyn.Sub * answer)

   type answstate = new | repeated

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

