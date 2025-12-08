(* Substitution Trees *)
(* Author: Brigitte Pientka *)

module type SUBTREE =
sig

  (*! module IntSyn : INTSYN !*)
  (*! module CompSyn : COMPSYN     !*)
  (*! module RBSet : RBSET  !*)

  type nvar = int      (* index for normal variables *)
  type bvar = int      (* index for bound variables *)
  type bdepth = int    (* depth of locally bound variables *)

  (* normal (linear) substitutions *)
(*  type normalSubsts = (IntSyn.Dec IntSyn.ctx * IntSyn.exp) RBSet.ordSet *)
  type typeLabel = TypeLabel | Body
  type normalSubsts =  (typeLabel * IntSyn.exp) RBSet.ordSet 
  type querySubsts = (IntSyn.Dec IntSyn.ctx * (typeLabel * IntSyn.exp)) RBSet.ordSet 

  type cGoal = CGoals of CompSyn.AuxGoal * IntSyn.cid  * CompSyn.Conjunction * int

  (* assignable (linear) subsitutions *)
  type assSub = Assign of IntSyn.Dec IntSyn.ctx * IntSyn.exp
  type assSubsts = AssSub RBSet.ordSet  (* key = int = bvar *) 

  type cnstr = Eqn of IntSyn.Dec IntSyn.ctx * IntSyn.exp * IntSyn.exp
      
  type tree = 
    Leaf of normalSubsts *  IntSyn.Dec IntSyn.ctx * CGoal
  | Node of normalSubsts * Tree RBSet.ordSet

(*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.ctx * CGoal *)

  val indexArray : ((int ref) * (Tree ref)) Array.array

  val sProgReset : unit -> unit
  val sProgInstall : (IntSyn.cid * CompSyn.CompHead * CompSyn.Conjunction) -> unit
  val matchSig : IntSyn.cid * IntSyn.Dec IntSyn.ctx * IntSyn.eclo * 
    ((CompSyn.Conjunction * IntSyn.Sub) * IntSyn.cid -> unit) -> unit 

(*  val goalToString : string -> IntSyn.Dec IntSyn.ctx * CompSyn.Goal * IntSyn.Sub -> string *)

end;; (* module type SUBTREE *)

