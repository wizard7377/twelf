(* Elim *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:39:26 2006 *)

module Elim
  (Data : DATA)
   (*! module IntSyn' : INTSYN !*)
   (*! module Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   module State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   (Abstract : ABSTRACT)
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   (TypeCheck : TYPECHECK)
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   (Whnf : WHNF)
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   (Unify : UNIFY): ELIM =
   (*! sharing Unify.IntSyn = IntSyn' !*)

struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Tomega = Tomega' !*)
  module State = State'

  exception Error of string

  type operator =
    Local of Tomega.Prg * int

  local
    module S = State
    module T = Tomega
    module I = IntSyn

    exception Success of int

(* These lines need to move *)

    (* fun stripTC (T.Abs (_, TC)) = TC *)
    fun stripTC TC = TC


    let rec stripTCOpt = function NONE -> NONE
      | (SOME TC) -> SOME (stripTC TC)

    let rec stripDec = function (T.UDec D) -> T.UDec D
      | (T.PDec (name, F, TC1, TC2)) -> T.PDec (name, F, TC1, stripTCOpt TC2)

    let rec strip = function I.Null -> I.Null
      | (I.Decl (Psi, D)) -> I.Decl (strip Psi, stripDec D)


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S.Focus (Y as T.EVar (Psi, r, G, V, _, _), W)) =   (* Y is lowered *)
      let
        let rec matchCtx = function (I.Null, _, Fs) -> Fs
          | (I.Decl (G, T.PDec (x, F, _, _)), n, Fs) -> 
          matchCtx (G, n+1, Local (Y, n) :: Fs)
          | (I.Decl (G, T.UDec _), n, Fs) -> 
          matchCtx (G, n+1, Fs)

      in
        matchCtx (Psi, 1, nil)
      end

    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
   let rec apply = function (Local (R as T.EVar (Psi, r, G, NONE, NONE, _), n)) -> 
       let
         let T.PDec (_, F0, _, _) = T.ctxDec (Psi, n)
       in
         (case F0
            of T.All ((T.UDec (I.Dec (_, V)), _), F) =>
             let
               let X = I.newEVar (T.coerceCtx (strip Psi), V)
               let I.NDec x = Names.decName (T.coerceCtx Psi, I.NDec NONE)
               let D = T.PDec (x, T.forSub (F, T.Dot (T.Exp X, T.id)), NONE, NONE)
               (* the NONE, NONE may breach an invariant *)
               (* revisit when we add subterm orderings *)
               let Psi' = I.Decl (Psi, D)
               let Y = T.newEVar (strip Psi', T.forSub (G, T.shift))
             in
               (r := SOME (T.Let (D, T.Redex (T.Var n, T.AppExp (X, T.Nil)), Y)))
             end
         | T.Ex ((D1, _), F) =>
             let
               let D1' = Names.decName (T.coerceCtx Psi, D1)
               let Psi' = I.Decl (Psi, T.UDec D1')
               let I.NDec x = Names.decName (T.coerceCtx (Psi'), I.NDec NONE)
               let D2 = T.PDec (x, F, NONE, NONE)
               let Psi'' = I.Decl (Psi', D2)
               let Y = T.newEVar (strip Psi'', T.forSub (G, T.Shift 2))
             in
               (r := SOME (T.LetPairExp (D1', D2, T.Var n, Y)))
             end
         | T.True =>
             let
               let Y = T.newEVar (strip Psi, G)
             in
               (r := SOME (T.LetUnit (T.Var n, Y)))
             end)
       end
      | (Local (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2, X), n)) -> 
           apply (Local (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2, X), n))


    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu (Local (X as T.EVar (Psi, _, _, _, _, _), n)) =
        (case (I.ctxLookup (Psi, n))
          of T.PDec (SOME x, _, _, _) =>
            ("Elim " ^ TomegaPrint.nameEVar X  ^ " with variable " ^ x))
           (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)

  in
    let expand = expand
    let apply = apply
    let menu = menu
  end (* local *)
end;; (* functor elim *)
