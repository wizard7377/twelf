(* Substitution Trees *)

(* Author: Brigitte Pientka *)

module type SUBTREE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN     !*)
  (*! structure RBSet : RBSET  !*)
  type nvar = int

  (* index for_sml normal variables *)
  type bvar = int

  (* index for_sml bound variables *)
  type bdepth = int

  (* depth of locally bound variables *)
  (* normal (linear) substitutions *)
  (*  type normalSubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet *)
  type typeLabel = TypeLabel | Body
  type normalSubsts = typeLabel * IntSyn.exp RBSet.ordSet

  type querySubsts =
    IntSyn.dec IntSyn.ctx * (typeLabel * IntSyn.exp) RBSet.ordSet

  type cGoal =
    | CGoals of CompSyn.auxGoal * IntSyn.cid * CompSyn.conjunction * int

  (* assignable (linear) subsitutions *)
  type assSub = Assign of IntSyn.dec IntSyn.ctx * IntSyn.exp
  type assSubsts = assSub RBSet.ordSet

  (* key = int = bvar *)
  type cnstr = Eqn of IntSyn.dec IntSyn.ctx * IntSyn.exp * IntSyn.exp

  type tree =
    | Leaf of normalSubsts * IntSyn.dec IntSyn.ctx * cGoal
    | Node of normalSubsts * tree RBSet.ordSet

  (*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *)
  val indexArray : int ref * tree ref Array.array
  val sProgReset : unit -> unit
  val sProgInstall : IntSyn.cid * CompSyn.compHead * CompSyn.conjunction -> unit

  val matchSig :
    IntSyn.cid
    * IntSyn.dec IntSyn.ctx
    * IntSyn.eclo
    * ((CompSyn.conjunction * IntSyn.sub) * IntSyn.cid -> unit) ->
    unit
  (*  val goalToString : string -> IntSyn.Dec IntSyn.Ctx * CompSyn.Goal * IntSyn.Sub -> string *)
end

(* signature SUBTREE *)
