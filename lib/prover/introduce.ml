(* Introduce *)

(* Author: Carsten Schuermann *)

module Introduce (State' : STATE) (TomegaNames : TOMEGANAMES) : INTRODUCE =
struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module State = State'
  module S = State'
  module T = Tomega
  module I = IntSyn

  exception Error

  type operator = T.prg * T.prg
  (*    fun stripTC (T.Abs (_, TC)) = TC *)

  let rec stripTC TC = TC
  let rec stripTCOpt = function None -> None | Some TC -> Some (stripTC TC)

  let rec stripDec = function
    | T.UDec D -> T.UDec D
    | T.PDec (name, F, TC1, TC2) -> T.PDec (name, F, TC1, stripTCOpt TC2)

  let rec strip = function
    | I.Null -> I.Null
    | I.Decl (Psi, D) -> I.Decl (strip Psi, stripDec D)
  (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)

  let rec expand = function
    | S.Focus (R, W) ->
        let D' = TomegaNames.decName (Psi, D) in
        Some (R, T.Lam (D', T.newEVar (I.Decl (strip Psi, D'), F)))
    | S.Focus (R, W) ->
        let X = I.newEVar (T.coerceCtx Psi, V) in
        let Y = T.newEVar (Psi, T.forSub (F, T.Dot (T.Exp X, T.id))) in
        Some (R, T.PairExp (X, Y))
    | S.Focus (R, W) -> Some (R, T.Unit)
    | S.Focus (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2, X), W) ->
        expand (S.Focus (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2, X), W))
    | S.Focus (T.EVar (Psi, r, _, _, _, _), W) -> None
  (* apply O = S

       Invariant:
       O = S
    *)

  let rec apply (T.EVar (_, r, _, _, _, _), P) = r := Some P
  (* need to trail for_sml back *)

  (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)

  let rec menu (r, P) = "Intro " ^ TomegaPrint.nameEVar r

  exception ErrorError

  type operator = operator

  let expand = expand
  let apply = apply
  let menu = menu
end
