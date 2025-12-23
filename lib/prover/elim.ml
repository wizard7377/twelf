(* ELIM: Version 1.4 *)

(* Author: Carsten Schuermann *)

module type ELIM = sig
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end

(* signature ELIM *)
(* Elim *)

(* Author: Carsten Schuermann *)

(* Date: Thu Mar 16 13:39:26 2006 *)

module Elim
    (Data : Data.DATA)
    (State' : State.STATE)
    (Abstract : Abstract.ABSTRACT)
    (TypeCheck : Typecheck.TYPECHECK)
    (Whnf : Whnf.WHNF)
    (Unify : Unify.UNIFY) : ELIM = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module State = State'

  exception Error of string

  type operator = Local of Tomega.prg * int
  type operator = operator

  module S = State
  module T = Tomega
  module I = IntSyn

  exception Success of int
  (* These lines need to move *)

  (* fun stripTC (T.Abs (_, TC)) = TC *)

  let rec stripTC TC = TC
  let rec stripTCOpt = function None -> None | Some TC -> Some (stripTC TC)

  let rec stripDec = function
    | T.UDec D -> T.UDec D
    | T.PDec (name, F, TC1, TC2) -> T.PDec (name, F, TC1, stripTCOpt TC2)

  let rec strip = function
    | I.Null -> I.Null
    | I.Decl (Psi, D) -> I.Decl (strip Psi, stripDec D)
  (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)

  let rec expand (S.Focus (Y, W)) =
    (* Y is lowered *)
    let rec matchCtx = function
      | I.Null, _, Fs -> Fs
      | I.Decl (G, T.PDec (x, F, _, _)), n, Fs ->
          matchCtx (G, n + 1, Local (Y, n) :: Fs)
      | I.Decl (G, T.UDec _), n, Fs -> matchCtx (G, n + 1, Fs)
    in
    matchCtx (Psi, 1, [])
  (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)

  let rec apply = function
    | Local (R, n) -> (
        let (T.PDec (_, F0, _, _)) = T.ctxDec (Psi, n) in
        match F0 with
        | T.All ((T.UDec (I.Dec (_, V)), _), F) ->
            (* the NONE, NONE may breach an invariant *)
            (* revisit when we add subterm orderings *)
            let X = I.newEVar (T.coerceCtx (strip Psi), V) in
            let (I.NDec x) = Names.decName (T.coerceCtx Psi, I.NDec None) in
            let D =
              T.PDec (x, T.forSub (F, T.Dot (T.Exp X, T.id)), None, None)
            in
            let Psi' = I.Decl (Psi, D) in
            let Y = T.newEVar (strip Psi', T.forSub (G, T.shift)) in
            r := Some (T.Let (D, T.Redex (T.Var n, T.AppExp (X, T.Nil)), Y))
        | T.Ex ((D1, _), F) ->
            let D1' = Names.decName (T.coerceCtx Psi, D1) in
            let Psi' = I.Decl (Psi, T.UDec D1') in
            let (I.NDec x) = Names.decName (T.coerceCtx Psi', I.NDec None) in
            let D2 = T.PDec (x, F, None, None) in
            let Psi'' = I.Decl (Psi', D2) in
            let Y = T.newEVar (strip Psi'', T.forSub (G, T.Shift 2)) in
            r := Some (T.LetPairExp (D1', D2, T.Var n, Y))
        | T.True ->
            let Y = T.newEVar (strip Psi, G) in
            r := Some (T.LetUnit (T.Var n, Y)))
    | Local (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2, X), n) ->
        apply (Local (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2, X), n))
  (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)

  let rec menu (Local (X, n)) =
    match I.ctxLookup (Psi, n) with
    | T.PDec (Some x, _, _, _) ->
        "Elim " ^ TomegaPrint.nameEVar X ^ " with variable " ^ x
  (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)

  let expand = expand
  let apply = apply
  let menu = menu
  (* local *)
end

(* functor elim *)
