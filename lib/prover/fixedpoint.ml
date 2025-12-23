(* Splitting: Version 1.4 *)

(* Author: Carsten Schuermann *)

module type FIXEDPOINT = sig
  (*! structure IntSyn : Intsyn.INTSYN !*)
  (*! structure Tomega : Tomega.TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus * Tomega.tC -> operator
  val apply : operator -> unit
  val menu : operator -> string
end

(* signature Fixed Point *)
(* Fixed Point *)

(* Author: Carsten Schuermann *)

module FixedPoint (State' : State.STATE) : FIXEDPOINT = struct
  (*! structure IntSyn = IntSyn' !*)

  (*! structure Tomega = Tomega' !*)

  module State = State'
  module S = State'
  module T = Tomega
  module I = IntSyn

  exception Error

  type operator = T.prg option ref * T.prg
  (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)

  let rec expand (S.Focus (T.EVar (Psi, r, F, _, TCs, _), W), O) =
    (*        val D = T.PDec (SOME "IH" , F, SOME O, SOME O) *)
    let (I.NDec x) = Names.decName (T.coerceCtx Psi, I.NDec None) in
    let D = T.PDec (x, F, None, None) in
    let X = T.newEVar (I.Decl (Psi, D), T.forSub (F, T.Shift 1)) in
    (r, T.Rec (D, X))
  (* apply O = S

       Invariant:
       O = S
    *)

  let rec apply (r, P) = r := Some P
  (* should be trailed -cs Thu Apr 22 11:20:32 2004 *)

  (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)

  let rec menu _ = "Recursion introduction"

  exception ErrorError

  type operator = operator

  let expand = expand
  let apply = apply
  let menu = menu
end
