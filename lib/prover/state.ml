(* State definition for_sml Proof Search *)

(* Author: Carsten Schuermann *)

module type STATE = sig
  exception Error of string

  type state =
    | State of
        Tomega.worlds * Tomegas.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml
    | StateLF of IntSyn.exp

  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp

  (* focus EVar *)
  val init : Tomega.for_sml * Tomega.worlds -> state
  val close : state -> bool
  val collectT : Tomega.prg -> Tomega.prg list
  val collectLF : Tomega.prg -> IntSyn.exp list
  val collectLFSub : Tomega.sub -> IntSyn.exp list
end
(* State definition for_sml Proof Search *)

(* Author: Carsten Schuermann *)

module State (Formatter : Formatter.FORMATTER) : STATE = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module Formatter = Formatter

  type state =
    | State of
        Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg * Tomega.for_sml
    | StateLF of IntSyn.exp
  (* StateLF X, X is always lowered *)

  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp
  (* datatype State
    = State of (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds
 *)

  (*  datatype SideCondition  (* we need some work here *)
    = None
    | All   of SideCondition
    | And   of SideCondition * SideCondition
    | Order of Order.Predicate
*)

  exception Error of string

  module T = Tomega
  module I = IntSyn
  (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)

  let rec findPrg = function
    | T.Lam (_, P) -> findPrg P
    | T.New P -> findPrg P
    | T.Choose P -> findPrg P
    | T.PairExp (_, P) -> findPrg P
    | T.PairBlock (B, P) -> findPrg P
    | T.PairPrg (P1, P2) -> findPrg P1 @ findPrg P2
    | T.Unit -> []
    | T.Rec (_, P) -> findPrg P
    | T.Case (T.Cases C) -> findCases C
    | T.PClo (P, t) -> findPrg P @ findSub t
    | T.Let (D, P1, P2) -> findPrg P1 @ findPrg P2
    | T.LetPairExp (D1, D2, P1, P2) -> findPrg P1 @ findPrg P2
    | T.LetUnit (P1, P2) -> findPrg P1 @ findPrg P2
    | X -> [ X ]
    | X -> findPrg P
    | T.Const _ -> []
    | T.Var _ -> []
    | T.Redex (P, S) -> findPrg P @ findSpine S

  and findCases = function
    | [] -> []
    | (_, _, P) :: C -> findPrg P @ findCases C

  and findSub = function
    | T.Shift _ -> []
    | T.Dot (F, t) -> findFront F @ findSub t

  and findFront = function
    | T.Idx _ -> []
    | T.Prg P -> findPrg P
    | T.Exp _ -> []
    | T.Block _ -> []
    | T.Undef -> []

  and findSpine = function
    | T.Nil -> []
    | T.AppPrg (P, S) -> findPrg P @ findSpine S
    | T.AppExp (_, S) -> findSpine S
    | T.AppBlock (_, S) -> findSpine S
  (* by invariant: blocks don't contain free evars *)

  (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)

  let rec findExp = function
    | (Psi, T.Lam (D, P)), K -> findExp (I.Decl (Psi, D), P) K
    | (Psi, T.New P), K -> findExp (Psi, P) K
    | (Psi, T.Choose P), K -> findExp (Psi, P) K
    | (Psi, T.PairExp (M, P)), K ->
        findExp (Psi, P) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K))
    | (Psi, T.PairBlock (B, P)), K -> findExp (Psi, P) K
    | (Psi, T.PairPrg (P1, P2)), K -> findExp (Psi, P2) (findExp (Psi, P1) K)
    | (Psi, T.Unit), K -> K
    | (Psi, T.Rec (D, P)), K -> findExp (Psi, P) K
    | (Psi, T.Case (T.Cases C)), K -> findExpCases (Psi, C) K
    | (Psi, T.PClo (P, t)), K -> findExpSub (Psi, t) (findExp (Psi, P) K)
    | (Psi, T.Let (D, P1, P2)), K ->
        findExp (I.Decl (Psi, D), P2) (findExp (Psi, P1) K)
    | (Psi, T.LetPairExp (D1, D2, P1, P2)), K ->
        findExp (I.Decl (I.Decl (Psi, T.UDec D1), D2), P2) (findExp (Psi, P1) K)
    | (Psi, T.LetUnit (P1, P2)), K -> findExp (Psi, P2) (findExp (Psi, P1) K)
    | (Psi, X), K -> K
    | (Psi, T.Const _), K -> K
    | (Psi, T.Var _), K -> K
    | (Psi, T.Redex (P, S)), K -> findExpSpine (Psi, S) K

  and findExpSpine = function
    | (Psi, T.Nil), K -> K
    | (Psi, T.AppPrg (_, S)), K -> findExpSpine (Psi, S) K
    | (Psi, T.AppExp (M, S)), K ->
        findExpSpine (Psi, S)
          (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K))
    | (Psi, T.AppBlock (_, S)), K -> findExpSpine (Psi, S) K

  and findExpCases = function
    | (Psi, []), K -> K
    | (Psi, (_, _, P) :: C), K -> findExpCases (Psi, C) (findExp (Psi, P) K)

  and findExpSub = function
    | (Psi, T.Shift _), K -> K
    | (Psi, T.Dot (F, t)), K -> findExpSub (Psi, t) (findExpFront (Psi, F) K)

  and findExpFront = function
    | (Psi, T.Idx _), K -> K
    | (Psi, T.Prg P), K -> findExp (Psi, P) K
    | (Psi, T.Exp M), K -> Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K)
    | (Psi, T.Block _), K -> K
    | (Psi, T.Undef), K -> K
  (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)

  let rec init (F, W) =
    let X = T.newEVar (I.Null, F) in
    State (W, I.Null, X, F)
  (* close S = B

       Invariant:
       If  B holds iff S  doesn't contain any free subgoals
    *)

  let rec close (State (W, _, P, _)) =
    match (findPrg P, findExp (I.Null, P) []) with [], [] -> true | _ -> false

  let close = close
  let init = init
  let collectT = findPrg
  let collectLF = fun P -> findExp (I.Null, P) []
  let collectLFSub = fun s -> findExpSub (I.Null, s) []
end
