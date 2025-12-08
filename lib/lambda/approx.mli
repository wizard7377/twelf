(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)

module type APPROX =
sig

  (*! module IntSyn : INTSYN !*)

  type uni =
      Level of int (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)
    | Next of uni
    | LVar of uni option ref
              
  type exp =
      Uni of uni
    | Arrow of exp * exp 
    | Const of IntSyn.Head (* Const/Def/NSDef *)
    | CVar of exp option ref
    | Undefined

  val Type : Uni
  val Kind : Uni
  val Hyperkind : Uni

  (* resets names of undetermined type/kind variables chosen for printing *)
  val varReset : unit -> unit

  val newLVar : unit -> Uni
  val newCVar : unit -> Exp

  val whnfUni : Uni -> Uni
  val whnf : Exp -> Exp

  val uniToApx : IntSyn.Uni -> Uni
  val classToApx : IntSyn.exp -> Exp * Uni
  val exactToApx : IntSyn.exp * IntSyn.exp -> Exp * Exp * Uni

  exception Ambiguous
  val apxToUni : Uni -> IntSyn.Uni
  val apxToClass : IntSyn.dctx * Exp * Uni * bool -> IntSyn.exp
  val apxToExact : IntSyn.dctx * Exp * IntSyn.eclo * bool -> IntSyn.exp

  exception Unify of string
  val matchUni : Uni * Uni -> unit
  val match : Exp * Exp -> unit

  val makeGroundUni : Uni -> bool

end
