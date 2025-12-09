(* Introduce *)
(* Author: Carsten Schuermann *)

module Introduce
  ((*! module IntSyn' : INTSYN !*)
   (*! module Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   module State' : STATE
   (TomegaNames : TOMEGANAMES): INTRODUCE =
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
struct
  (*! module IntSyn = IntSyn' !*)
  (*! module Tomega = Tomega' !*)
  module State = State'

  local
  module S = State'
  module T = Tomega
  module I = IntSyn

    exception Error = S.Error
    type operator = T.Prg * T.Prg

(*    fun stripTC (T.Abs (_, TC)) = TC *)
      let rec stripTC TC = TC


    let rec stripTCOpt = function NONE -> NONE
      | (SOME TC) -> SOME (stripTC TC)

    let rec stripDec = function (T.UDec D) -> T.UDec D
      | (T.PDec (name, F, TC1, TC2)) -> T.PDec (name, F, TC1, stripTCOpt TC2)

    let rec strip = function I.Null -> I.Null
      | (I.Decl (Psi, D)) -> I.Decl (strip Psi, stripDec D)


    (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
    let rec expand = function (S.Focus (R as T.EVar (Psi, r, T.All ((D, _), F), NONE, NONE, _), W)) -> 
        let
          let D' = TomegaNames.decName (Psi, D)
        in
          SOME (R, T.Lam (D', T.newEVar (I.Decl (strip Psi, D'), F)))
        end
      | (S.Focus (R as T.EVar (Psi, r, T.Ex ((D as I.Dec (_, V), _), F), NONE, NONE, _), W)) -> 
           let
             let X = I.newEVar (T.coerceCtx (Psi), V)
             let Y = T.newEVar (Psi, T.forSub (F, T.Dot (T.Exp X, T.id)))
           in
             SOME (R, T.PairExp (X, Y))
           end
      | (S.Focus (R as T.EVar (Psi, r, T.True, NONE, NONE, _), W)) -> 
           (SOME (R, T.Unit))

      | (S.Focus (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2, X), W)) -> 
           expand (S.Focus (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2, X), W))
      | (S.Focus (T.EVar (Psi, r, _, _, _, _), W)) -> NONE

    (* apply O = S

       Invariant:
       O = S
    *)
    let rec apply (T.EVar (_, r, _, _, _, _), P) = (r := SOME P)   (* need to trail for back *)

    (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
    let rec menu (r, P) = "Intro " ^ TomegaPrint.nameEVar r


  in
    exception Error = Error
    type operator = operator

    let expand = expand
    let apply = apply
    let menu =menu
  end
end