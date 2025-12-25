open Basis
(* Normalizer for_sml Delphin meta level *)

(* Author: Carsten Schuermann *)

module type NORMALIZE = sig
  module IntSyn : Intsyn.INTSYN
  module Tomega : Tomega.TOMEGA

  val normalizeFor : Tomega.for_sml * Tomega.sub -> Tomega.for_sml
  val normalizePrg : Tomega.prg * Tomega.sub -> Tomega.prg
  val normalizeSpine : Tomega.spine * Tomega.sub -> Tomega.spine
  val normalizeSub : Tomega.sub -> Tomega.sub
end
(* Internal syntax for_sml functional proof term calculus *)

(* Author: Carsten Schuermann *)

module Normalize
    (IntSyn' : Intsyn.INTSYN)
    (Tomega' : Tomega.TOMEGA)
    (Whnf : Whnf.WHNF) : Normalize.NORMALIZE = struct
  module IntSyn = IntSyn'
  module Tomega = Tomega'

  exception Error of string

  module I = IntSyn'
  module T = Tomega'

  let rec normalizeFor = function
    | T.All (D, F), t -> T.All (T.decSub (D, t), normalizeFor (F, T.dot1 t))
    | T.Ex (D, F), t ->
        T.Ex (I.decSub (D, T.coerceSub t), normalizeFor (F, T.dot1 t))
    | T.And (F1, F2), t -> T.And (normalizeFor (F1, t), normalizeFor (F2, t))
    | T.FClo (F, t1), t2 -> normalizeFor (F, T.comp (t1, t2))
    | T.World (W, F), t -> T.World (W, normalizeFor (F, t))
    | T.True, _ -> T.True
  (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for_sml
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

  let rec normalizePrg = function
    | P, t -> P
    | P, t -> normalizePrg (P, T.Dot (T.varSub (n, t), T.id))
    | T.Lam (D, P'), t -> T.Lam (D, normalizePrg (P', T.dot1 t))
    | T.PairExp (U, P'), t ->
        T.PairExp
          ( I.EClo (Whnf.whnf ((U, T.coerceSub t) : I.eclo)),
            normalizePrg (P', t) )
    | T.PairPrg (P1, P2), t ->
        T.PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
    | T.Unit, _ -> T.Unit
    | T.Redex (P, S), t -> T.Redex (normalizePrg (P, t), normalizeSpine S)
    | T.Rec (D, P), t -> T.Rec (D, normalizePrg (P, t))
    | P, t -> P
    | P, t -> normalizePrg (P', t)

  and normalizeSpine = function
    | T.Nil -> T.Nil
    | T.AppExp (U, S) -> T.AppExp (U, normalizeSpine S)
    | T.AppPrg (P, S) -> T.AppPrg (normalizePrg (P, T.id), normalizeSpine S)
    | T.AppBlock (B, S) -> T.AppBlock (B, normalizeSpine S)
  (*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)

  let rec normalizeSub = function
    | s -> s
    | T.Dot (T.Prg P, s) ->
        T.Dot (T.Prg (normalizePrg (P, T.id)), normalizeSub s)
    | T.Dot (F, s) -> T.Dot (F, normalizeSub s)

  let normalizeFor = normalizeFor
  let normalizePrg = normalizePrg
  let normalizeSpine = normalizeSpine
  let normalizeSub = normalizeSub
end
