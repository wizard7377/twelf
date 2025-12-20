(* Internal syntax for_sml functional proof term calculus *)


(* Author: Carsten Schuermann *)


module Normalize (Whnf : WHNF) : NORMALIZE = struct (*! structure IntSyn = IntSyn' !*)

(*! structure Tomega = Tomega' !*)

exception Error of string
module I = IntSyn
module T = Tomega
let rec normalizeFor = function (T.All ((D, Q), F), t) -> T.All ((T.decSub (D, t), Q), normalizeFor (F, T.dot1 t)) | (T.Ex ((D, Q), F), t) -> T.Ex ((I.decSub (D, T.coerceSub t), Q), normalizeFor (F, T.dot1 t)) | (T.And (F1, F2), t) -> T.And (normalizeFor (F1, t), normalizeFor (F2, t)) | (T.FClo (F, t1), t2) -> normalizeFor (F, T.comp (t1, t2)) | (T.World (W, F), t) -> T.World (W, normalizeFor (F, t)) | (T.True, _) -> T.True
let rec whnfFor = function (Ft) -> Ft | (Ft) -> Ft | (Ft) -> Ft | (T.FClo (F, t1), t2) -> whnfFor (F, T.comp (t1, t2)) | (Ft) -> Ft | (Ft) -> Ft
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

let rec normalizePrg = function (T.Var n, t) -> (match T.varSub (n, t) with (T.Prg P) -> P | (T.Idx _) -> raise (Domain) | (T.Exp _) -> raise (Domain) | (T.Block _) -> raise (Domain) | (T.Undef) -> raise (Domain)) | (T.PairExp (U, P'), t) -> T.PairExp (Whnf.normalize (U, T.coerceSub t), normalizePrg (P', t)) | (T.PairBlock (B, P'), t) -> T.PairBlock (I.blockSub (B, T.coerceSub t), normalizePrg (P', t)) | (T.PairPrg (P1, P2), t) -> T.PairPrg (normalizePrg (P1, t), normalizePrg (P2, t)) | (T.Unit, _) -> T.Unit | (T.EVar (_, { contents = (Some P) }, _), t) -> T.PClo (P, t) | (P, t) -> T.PClo (P, t) | (T.PClo (P, t), t') -> normalizePrg (P, T.comp (t, t'))
and normalizeSpine = function (T.Nil, t) -> T.Nil | (T.AppExp (U, S), t) -> T.AppExp (Whnf.normalize (U, T.coerceSub t), normalizeSpine (S, t)) | (T.AppPrg (P, S), t) -> T.AppPrg (normalizePrg (P, t), normalizeSpine (S, t)) | (T.AppBlock (B, S), t) -> T.AppBlock (I.blockSub (B, T.coerceSub t), normalizeSpine (S, t)) | (T.SClo (S, t1), t2) -> normalizeSpine (S, T.comp (t1, t2))
(*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)

let rec normalizeSub = function (s) -> s | (T.Dot (T.Prg P, s)) -> T.Dot (T.Prg (normalizePrg (P, T.id)), normalizeSub s) | (T.Dot (T.Exp E, s)) -> T.Dot (T.Exp (Whnf.normalize (E, I.id)), normalizeSub s) | (T.Dot (T.Block k, s)) -> T.Dot (T.Block k, normalizeSub s) | (T.Dot (T.Idx k, s)) -> T.Dot (T.Idx k, normalizeSub s)
let normalizeFor = normalizeFor
let normalizePrg = normalizePrg
let normalizeSub = normalizeSub
let whnfFor = whnfFor
 end
