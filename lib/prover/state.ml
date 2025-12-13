(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) State
  (structure Formatter : FORMATTER) : STATE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure Formatter = Formatter

  datatype state =
    State of Tomega.worlds
      * Tomega.dec IntSyn.ctx * Tomega.prg * Tomega.for
  | StateLF of IntSyn.exp    (* StateLF X, X is always lowered *)

  datatype focus =
    Focus of Tomega.prg * Tomega.worlds
  | FocusLF of IntSyn.exp

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

  local
    structure T = Tomega
    structure I = IntSyn



    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    fun (* GEN BEGIN FUN FIRST *) findPrg (T.Lam (_, P)) = findPrg P (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.New P) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Choose P) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.PairExp (_, P)) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.PairBlock (B, P)) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.PairPrg (P1, P2)) = findPrg P1 @ findPrg P2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Unit) = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Rec (_, P)) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Case (T.Cases C)) = findCases C (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.PClo (P, t)) = findPrg P @ findSub t (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Let (D, P1, P2)) = findPrg P1 @ findPrg P2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.LetPairExp (D1, D2, P1, P2)) = findPrg P1 @ findPrg P2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.LetUnit (P1, P2)) = findPrg P1 @ findPrg P2 (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (X as T.EVar (_, ref NONE, _, _, _, _)) = [X] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (X as T.EVar (_, ref (SOME P), _, _, _, _)) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Const _) = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Var _) = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findPrg (T.Redex (P, S)) = findPrg P @ findSpine S (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) findCases nil = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findCases ((_, _, P) :: C) = findPrg P @ findCases C (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) findSub (T.Shift _) = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findSub (T.Dot (F, t)) = findFront F @ findSub t (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) findFront (T.Idx _) = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findFront (T.Prg P) = findPrg P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findFront (T.Exp _) = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findFront (T.Block _) = [] (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findFront (T.Undef) = [] (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) findSpine (T.Nil) = [] (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findSpine (T.AppPrg (P, S)) = findPrg P @ findSpine S (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findSpine (T.AppExp (_, S)) = findSpine S (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findSpine (T.AppBlock (_, S)) = findSpine S (* GEN END FUN BRANCH *)   (* by invariant: blocks don't contain free evars *)

    (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
    fun (* GEN BEGIN FUN FIRST *) findExp (Psi, T.Lam (D, P)) K = findExp (I.Decl (Psi, D), P) K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.New P) K = findExp (Psi, P) K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Choose P) K = findExp (Psi, P) K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.PairExp (M, P)) K =
          findExp (Psi, P) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.PairBlock (B, P)) K = findExp (Psi, P) K (* GEN END FUN BRANCH *)
          (* by invariant: Blocks don't contain free evars. *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.PairPrg (P1, P2)) K = findExp (Psi, P2) (findExp (Psi, P1) K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Unit) K = K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Rec (D, P)) K = findExp (Psi, P) K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Case (T.Cases C)) K = findExpCases (Psi, C) K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.PClo (P, t)) K =
          findExpSub (Psi, t) (findExp (Psi, P) K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Let (D, P1, P2)) K =
          findExp (I.Decl (Psi, D), P2) (findExp (Psi, P1) K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.LetPairExp (D1, D2, P1, P2)) K =
          findExp (I.Decl (I.Decl (Psi, T.UDec D1), D2), P2) (findExp (Psi, P1) K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.LetUnit (P1, P2)) K =
          findExp (Psi, P2) (findExp (Psi, P1) K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, X as T.EVar _) K = K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Const _) K = K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Var _) K = K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExp (Psi, T.Redex (P, S)) K = findExpSpine (Psi, S) K (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) findExpSpine (Psi, T.Nil) K = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findExpSpine (Psi, T.AppPrg (_, S)) K = findExpSpine (Psi, S) K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExpSpine (Psi, T.AppExp (M, S)) K = findExpSpine (Psi, S) (Abstract.collectEVars (T.coerceCtx Psi, (M, I.id), K)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExpSpine (Psi, T.AppBlock (_, S)) K = findExpSpine (Psi, S) K (* GEN END FUN BRANCH *)


    and (* GEN BEGIN FUN FIRST *) findExpCases (Psi, nil) K = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findExpCases (Psi, (_, _, P) :: C) K =
          findExpCases (Psi, C) (findExp (Psi, P) K) (* GEN END FUN BRANCH *)
    and (* GEN BEGIN FUN FIRST *) findExpSub (Psi, T.Shift _)  K = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findExpSub (Psi, T.Dot (F, t)) K =
          findExpSub (Psi, t) (findExpFront (Psi, F) K) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) findExpFront (Psi, T.Idx _) K  = K (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) findExpFront (Psi, T.Prg P) K = findExp (Psi, P) K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExpFront (Psi, T.Exp M) K =
          Abstract.collectEVars (T.coerceCtx Psi,  (M, I.id), K) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExpFront (Psi, T.Block _) K = K (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) findExpFront (Psi, T.Undef) K = K (* GEN END FUN BRANCH *)


    (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
    fun init (F, W) =
        let
          (* GEN BEGIN TAG OUTSIDE LET *) val X = T.newEVar (I.Null, F) (* GEN END TAG OUTSIDE LET *)
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
    (* GEN BEGIN TAG OUTSIDE LET *) val close = close (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val init = init (* GEN END TAG OUTSIDE LET *)

    (* GEN BEGIN TAG OUTSIDE LET *) val collectT = findPrg (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val collectLF = (* GEN BEGIN FUNCTION EXPRESSION *) fn P => findExp (I.Null, P) [] (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val collectLFSub = (* GEN BEGIN FUNCTION EXPRESSION *) fn s => findExpSub (I.Null, s) [] (* GEN END FUNCTION EXPRESSION *) (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *)