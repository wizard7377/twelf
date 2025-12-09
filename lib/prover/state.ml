(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

module State
  (Formatter : FORMATTER) : STATE =
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Tomega = Tomega' !*)
  module Formatter = Formatter

  type state =
    State of Tomega.Worlds
      * Tomega.Dec IntSyn.ctx * Tomega.Prg * Tomega.For
  | StateLF of IntSyn.exp    (* StateLF X, X is always lowered *)

  type focus =
    Focus of Tomega.Prg * Tomega.Worlds
  | FocusLF of IntSyn.exp

 (* type State
    = State of (Tomega.Dec IntSyn.ctx * Tomega.For) * Tomega.Worlds
 *)
(*  type SideCondition  (* we need some work here *)
    = None
    | All   of SideCondition
    | And   of SideCondition * SideCondition
    | Order of Order.Predicate
*)

  exception Error of string

  local
    module T = Tomega
    module I = IntSyn



    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    let rec findPrg = function (T.Lam (_, P)) -> findPrg P
      | (T.New P) -> findPrg P
      | (T.Choose P) -> findPrg P
      | (T.PairExp (_, P)) -> findPrg P
      | (T.PairBlock (B, P)) -> findPrg P
      | (T.PairPrg (P1, P2)) -> findPrg P1 @ findPrg P2
      | (T.Unit) -> []
      | (T.Rec (_, P)) -> findPrg P
      | (T.Case (T.Cases C)) -> findCases C
      | (T.PClo (P, t)) -> findPrg P @ findSub t
      | (T.Let (D, P1, P2)) -> findPrg P1 @ findPrg P2
      | (T.LetPairExp (D1, D2, P1, P2)) -> findPrg P1 @ findPrg P2
      | (T.LetUnit (P1, P2)) -> findPrg P1 @ findPrg P2
      | (X as T.EVar (_, ref NONE, _, _, _, _)) -> [X]
      | (X as T.EVar (_, ref (SOME P), _, _, _, _)) -> findPrg P
      | (T.Const _) -> []
      | (T.Var _) -> []
      | (T.Redex (P, S)) -> findPrg P @ findSpine S

    and findCases nil = []
      | findCases ((_, _, P) :: C) = findPrg P @ findCases C

    and findSub (T.Shift _) = []
      | findSub (T.Dot (F, t)) = findFront F @ findSub t

    and findFront (T.Idx _) = []
      | findFront (T.Prg P) = findPrg P
      | findFront (T.Exp _) = []
      | findFront (T.Block _) = []
      | findFront (T.Undef) = []

    and findSpine (T.Nil) = []
      | findSpine (T.AppPrg (P, S)) = findPrg P @ findSpine S
      | findSpine (T.AppExp (_, S)) = findSpine S
      | findSpine (T.AppBlock (_, S)) = findSpine S   (* by invariant: blocks don't contain free evars *)

    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    let rec findExp = function (Psi, T.Lam (D, P)) K -> findExp (I.Decl (Psi, D), P) K
      | (Psi, T.New P) K -> findExp (Psi, P) K
      | (Psi, T.Choose P) K -> findExp (Psi, P) K
      | (Psi, T.PairExp (M, P)) K -> 
          findExp (Psi, P) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K))
      | (Psi, T.PairBlock (B, P)) K -> findExp (Psi, P) K
          (* by invariant: Blocks don't contain free evars. *)
      | (Psi, T.PairPrg (P1, P2)) K -> findExp (Psi, P2) (findExp (Psi, P1) K)
      | (Psi, T.Unit) K -> K
      | (Psi, T.Rec (D, P)) K -> findExp (Psi, P) K
      | (Psi, T.Case (T.Cases C)) K -> findExpCases (Psi, C) K
      | (Psi, T.PClo (P, t)) K -> 
          findExpSub (Psi, t) (findExp (Psi, P) K)
      | (Psi, T.Let (D, P1, P2)) K -> 
          findExp (I.Decl (Psi, D), P2) (findExp (Psi, P1) K)
      | (Psi, T.LetPairExp (D1, D2, P1, P2)) K -> 
          findExp (I.Decl (I.Decl (Psi, T.UDec D1), D2), P2) (findExp (Psi, P1) K)
      | (Psi, T.LetUnit (P1, P2)) K -> 
          findExp (Psi, P2) (findExp (Psi, P1) K)
      | (Psi, X as T.EVar _) K -> K
      | (Psi, T.Const _) K -> K
      | (Psi, T.Var _) K -> K
      | (Psi, T.Redex (P, S)) K -> findExpSpine (Psi, S) K

    and findExpSpine (Psi, T.Nil) K = K
      | findExpSpine (Psi, T.AppPrg (_, S)) K = findExpSpine (Psi, S) K
      | findExpSpine (Psi, T.AppExp (M, S)) K = findExpSpine (Psi, S) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K))
      | findExpSpine (Psi, T.AppBlock (_, S)) K = findExpSpine (Psi, S) K


    and findExpCases (Psi, nil) K = K
      | findExpCases (Psi, (_, _, P) :: C) K =
          findExpCases (Psi, C) (findExp (Psi, P) K)
    and findExpSub (Psi, T.Shift _)  K = K
      | findExpSub (Psi, T.Dot (F, t)) K =
          findExpSub (Psi, t) (findExpFront (Psi, F) K)

    and findExpFront (Psi, T.Idx _) K  = K
      | findExpFront (Psi, T.Prg P) K = findExp (Psi, P) K
      | findExpFront (Psi, T.Exp M) K =
          Abstract.collectEVars (T.coerceCtx Psi,  (M, I.id), K)
      | findExpFront (Psi, T.Block _) K = K
      | findExpFront (Psi, T.Undef) K = K


    (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
    fun init (F, W) =
        let
          let X = T.newEVar (I.Null, F)
        in State (W, I.Null, X, F)
        end


    (* close S = B

       Invariant:
       If  B holds iff S  doesn't contain any free subgoals
    *)
    fun close (State (W, _, P, _)) =
         (case (findPrg P, findExp (I.Null, P) [])
            of (nil, nil) => true
             | _ => false)


  in
    let close = close
    let init = init

    let collectT = findPrg
    let collectLF = fun P -> findExp (I.Null, P) []
    let collectLFSub = fun s -> findExpSub (I.Null, s) []
  end
end