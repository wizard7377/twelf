(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor (* GEN BEGIN FUNCTOR DECL *) Normalize
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
) : NORMALIZE =
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'

  exception Error of string

  local
    structure I = IntSyn'
    structure T = Tomega'

    fun (* GEN BEGIN FUN FIRST *) normalizeFor (T.All (D, F), t) =
          T.All (T.decSub (D, t),
                 normalizeFor (F, T.dot1 t)) (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (T.Ex (D, F), t) =
          T.Ex (I.decSub (D, T.coerceSub t),
                 normalizeFor (F, T.dot1 t)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (T.And (F1, F2), t) =
          T.And (normalizeFor (F1, t),
                 normalizeFor (F2, t)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (T.FClo (F, t1), t2) =
          normalizeFor (F, T.comp (t1, t2)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (T.World (W, F), t) =
          T.World (W, normalizeFor (F, t)) (* GEN END FUN BRANCH *)
(*      | normalizeFor (T.FVar (G, r))   think about it *)
      | (* GEN BEGIN FUN BRANCH *) normalizeFor (T.True, _) = T.True (* GEN END FUN BRANCH *)


    (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

    fun (* GEN BEGIN FUN FIRST *) normalizePrg (P as (T.Root (T.Const _,_)), t) = P (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg ((P as (T.Root (T.Var n, _))), t) =
           normalizePrg (P, T.Dot (T.varSub (n, t), T.id)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (T.Lam (D, P'), t) = T.Lam (D, normalizePrg (P', T.dot1 t)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (T.PairExp (U, P'), t) =
          T.PairExp (I.EClo (Whnf.whnf ((U, T.coerceSub t) : I.eclo)), normalizePrg (P', t)) (* GEN END FUN BRANCH *)
(*      | normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (B, normalizePrg P') *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (T.PairPrg (P1, P2), t) =
          T.PairPrg (normalizePrg (P1, t), normalizePrg (P2, t)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (T.Unit, _) = T.Unit (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (T.Redex (P, S), t) =
          T.Redex (normalizePrg (P, t), normalizeSpine S) (* GEN END FUN BRANCH *)
          (* Clearly, the redex should be removed here *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (T.Rec (D, P), t) = T.Rec (D, normalizePrg (P, t)) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (P as T.Case _, t) = P (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizePrg (P as T.EVar (Psi, ref (SOME P'), _), t) = normalizePrg (P', t) (* GEN END FUN BRANCH *)

    and (* GEN BEGIN FUN FIRST *) normalizeSpine T.Nil = T.Nil (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizeSpine (T.AppExp (U, S)) =
          T.AppExp (U, normalizeSpine S) (* GEN END FUN BRANCH *)
     | (* GEN BEGIN FUN BRANCH *) normalizeSpine (T.AppPrg (P, S)) =
          T.AppPrg (normalizePrg (P, T.id), normalizeSpine S) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeSpine (T.AppBlock (B, S)) =
          T.AppBlock (B, normalizeSpine S) (* GEN END FUN BRANCH *)

(*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)

    fun (* GEN BEGIN FUN FIRST *) normalizeSub (s as T.Shift n) = s (* GEN END FUN FIRST *)
      | (* GEN BEGIN FUN BRANCH *) normalizeSub (T.Dot (T.Prg P, s)) =
          T.Dot (T.Prg (normalizePrg (P, T.id)), normalizeSub s) (* GEN END FUN BRANCH *)
      | (* GEN BEGIN FUN BRANCH *) normalizeSub (T.Dot (F, s)) =
          T.Dot (F, normalizeSub s) (* GEN END FUN BRANCH *)
  in
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizeFor = normalizeFor (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizePrg = normalizePrg (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizeSpine = normalizeSpine (* GEN END TAG OUTSIDE LET *)
    (* GEN BEGIN TAG OUTSIDE LET *) val normalizeSub = normalizeSub (* GEN END TAG OUTSIDE LET *)
  end
end (* GEN END FUNCTOR DECL *)
