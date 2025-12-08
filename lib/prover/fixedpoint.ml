(* Fixed Point *)
(* Author: Carsten Schuermann *)

module FixedPoint
  ((*! module IntSyn' : INTSYN !*)
   (*! module Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   module State' : STATE): FIXEDPOINT =
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
    type operator = (T.Prg option ref * T.Prg)


    (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)
    fun expand (S.Focus (T.EVar (Psi, r, F, _, TCs, _), W), O) =
        let
(*        let D = T.PDec (SOME "IH" , F, SOME O, SOME O) *)
          let I.NDec x = Names.decName (T.coerceCtx Psi, I.NDec NONE)
          let D = T.PDec (x, F, NONE, NONE)
          let X = T.newEVar (I.Decl (Psi, D), T.forSub (F, T.Shift 1))
        in
          (r, T.Rec (D, X))
        end

    (* apply O = S

       Invariant:
       O = S
    *)
    fun apply (r, P) = (r := SOME P)   (* should be trailed -cs Thu Apr 22 11:20:32 2004 *)

    (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
    fun menu _ = "Recursion introduction"


  in
    exception Error = Error
    type operator = operator

    let expand = expand
    let apply = apply
    let menu =menu
  end
end