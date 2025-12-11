(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor Normalize
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
) : NORMALIZE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega

    fun normalizeFor (T.All ((D, Q), F), t) =
          T.All ((T.decSub (D, t), Q),
                 normalizeFor (F, T.dot1 t))
      | (* GEN CASE BRANCH *) normalizeFor (T.Ex ((D, Q), F), t) =
          T.Ex ((I.decSub (D, T.coerceSub t), Q),
                 normalizeFor (F, T.dot1 t))
      | (* GEN CASE BRANCH *) normalizeFor (T.And (F1, F2), t) =
          T.And (normalizeFor (F1, t),
                 normalizeFor (F2, t))
      | (* GEN CASE BRANCH *) normalizeFor (T.FClo (F, t1), t2) =
          normalizeFor (F, T.comp (t1, t2))
      | (* GEN CASE BRANCH *) normalizeFor (T.World (W, F), t) =
          T.World (W, normalizeFor (F, t))
(*      | normalizeFor (T.FVar (G, r))   think about it *)
      | (* GEN CASE BRANCH *) normalizeFor (T.True, _) = T.True

    fun whnfFor (Ft as (T.All (D, _), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (Ft as (T.Ex (D, F), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (Ft as (T.And (F1, F2), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (T.FClo (F, t1), t2) =
          whnfFor (F, T.comp (t1, t2))
      | (* GEN CASE BRANCH *) whnfFor (Ft as (T.World (W, F), t)) = Ft
      | (* GEN CASE BRANCH *) whnfFor (Ft as (T.True, _)) = Ft


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

    fun normalizePrg (T.Var n, t) =
           (* ABP -- 1/20/03 *)
        (case T.varSub (n, t)
           of (T.Prg P) => P
           | (T.Idx _) => raise Domain
           | (T.Exp _) => raise Domain
           | (T.Block _) => raise Domain
           | (T.Undef) => raise Domain
             )
      |  (* GEN CASE BRANCH *) normalizePrg (T.PairExp (U, P'), t) =
          T.PairExp (Whnf.normalize (U, T.coerceSub t), normalizePrg (P', t))
      | (* GEN CASE BRANCH *) normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (I.blockSub (B, T.coerceSub t), normalizePrg (P', t))
      | (* GEN CASE BRANCH *) normalizePrg (T.PairPrg (P1, P2), t) =
          T.PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
      | (* GEN CASE BRANCH *) normalizePrg (T.Unit, _) = T.Unit


      | (* GEN CASE BRANCH *) normalizePrg (T.EVar (_, ref (SOME P), _), t) = T.PClo(P, t)

      (* ABP *)
      | (* GEN CASE BRANCH *) normalizePrg (P as T.EVar _, t) = T.PClo(P,t)

      | (* GEN CASE BRANCH *) normalizePrg (T.PClo (P, t), t') = normalizePrg (P, T.comp (t, t'))

    and normalizeSpine (T.Nil, t) = T.Nil
      | (* GEN CASE BRANCH *) normalizeSpine (T.AppExp (U, S), t) =
         T.AppExp (Whnf.normalize (U, T.coerceSub t), normalizeSpine (S, t))
      | (* GEN CASE BRANCH *) normalizeSpine (T.AppPrg (P, S), t) =
          T.AppPrg (normalizePrg (P, t), normalizeSpine (S, t))
      | (* GEN CASE BRANCH *) normalizeSpine (T.AppBlock (B, S), t) =
          T.AppBlock (I.blockSub (B, T.coerceSub t), normalizeSpine (S, t))
      | (* GEN CASE BRANCH *) normalizeSpine (T.SClo (S, t1), t2) =
          normalizeSpine (S, T.comp (t1, t2))

(*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)

    fun normalizeSub (s as T.Shift n) = s
      | (* GEN CASE BRANCH *) normalizeSub (T.Dot (T.Prg P, s)) =
          T.Dot (T.Prg (normalizePrg (P, T.id)), normalizeSub s)
      | (* GEN CASE BRANCH *) normalizeSub (T.Dot (T.Exp E, s)) =
          T.Dot (T.Exp (Whnf.normalize (E, I.id)), normalizeSub s)
      | (* GEN CASE BRANCH *) normalizeSub (T.Dot (T.Block k, s)) =
          T.Dot (T.Block k, normalizeSub s)
      | (* GEN CASE BRANCH *) normalizeSub (T.Dot (T.Idx k, s)) =
          T.Dot (T.Idx k, normalizeSub s)

  in
    val normalizeFor = normalizeFor
    val normalizePrg = normalizePrg
    val normalizeSub = normalizeSub
    val whnfFor = whnfFor
  end
end
