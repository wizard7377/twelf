(* Substitution Trees *)
(* Author: Brigitte Pientka *)

signature SUBTREE =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN     !*)
  (*! structure RBSet : RBSET  !*)

  type nvar = int      (* index for normal variables *)
  type bvar = int      (* index for bound variables *)
  type bdepth = int    (* depth of locally bound variables *)

  (* normal (linear) substitutions *)
(*  type normalSubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet *)
  datatype type_label = TypeLabel | Body
  type normal_substs =  (type_label * IntSyn.exp) RBSet.ord_set 
  type query_substs = (IntSyn.dec IntSyn.ctx * (type_label * IntSyn.exp)) RBSet.ord_set 

  datatype c_goal = CGoals of CompSyn.aux_goal * IntSyn.cid  * CompSyn.conjunction * int

  (* assignable (linear) subsitutions *)
  datatype ass_sub = Assign of IntSyn.dec IntSyn.ctx * IntSyn.exp
  type ass_substs = ass_sub RBSet.ord_set  (* key = int = bvar *) 

  datatype cnstr = Eqn of IntSyn.dec IntSyn.ctx * IntSyn.exp * IntSyn.exp
      
  datatype tree = 
    Leaf of normal_substs *  IntSyn.dec IntSyn.ctx * c_goal
  | Node of normal_substs * tree RBSet.ord_set

(*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *)

  val indexArray : ((int ref) * (tree ref)) Array.array

  val sProgReset : unit -> unit
  val sProgInstall : (IntSyn.cid * CompSyn.comp_head * CompSyn.conjunction) -> unit
  val matchSig : IntSyn.cid * IntSyn.dec IntSyn.ctx * IntSyn.eclo * 
    ((CompSyn.conjunction * IntSyn.sub) * IntSyn.cid -> unit) -> unit 

(*  val goalToString : string -> IntSyn.Dec IntSyn.Ctx * CompSyn.Goal * IntSyn.Sub -> string *)

end;  (* signature SUBTREE *)

