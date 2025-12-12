(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)

signature APPROX =
sig

  (*! structure IntSyn : INTSYN !*)

  datatype uni =
      Level of int (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)
    | Next of uni
    | LVar of uni option ref
              
  datatype exp =
      Uni of uni
    | Arrow of exp * exp 
    | Const of IntSyn.head (* Const/Def/NSDef *)
    | CVar of exp option ref
    | Undefined

  val Type : uni
  val Kind : uni
  val Hyperkind : uni

  (* resets names of undetermined type/kind variables chosen for printing *)
  val varReset : unit -> unit

  val newLVar : unit -> uni
  val newCVar : unit -> exp

  val whnfUni : uni -> uni
  val whnf : exp -> exp

  val uniToApx : IntSyn.uni -> uni
  val classToApx : IntSyn.exp -> exp * uni
  val exactToApx : IntSyn.exp * IntSyn.exp -> exp * exp * uni

  exception Ambiguous
  val apxToUni : uni -> IntSyn.uni
  val apxToClass : IntSyn.dctx * exp * uni * bool -> IntSyn.exp
  val apxToExact : IntSyn.dctx * exp * IntSyn.eclo * bool -> IntSyn.exp

  exception Unify of string
  val matchUni : uni * uni -> unit
  val match : exp * exp -> unit

  val makeGroundUni : uni -> bool

end
